{-# LANGUAGE CPP #-}
module Main where

import Control.Monad.IO.Class(liftIO)
import System.IO
import Text.Read

import App

#ifdef ENCLAVE
import Server as API
#else
import Client as API
#endif

-- * Return codes

retSuccess, passwordOutOfRange, walletAlreadyExists :: Int
retSuccess          = 0
passwordOutOfRange  = 1
walletAlreadyExists = 2

cannotSaveWallet, cannotLoadWallet, wrongMasterPassword :: Int
cannotSaveWallet    = 3
cannotLoadWallet    = 4
wrongMasterPassword = 5

walletFull, itemDoesNotExist, itemTooLong, failSeal, failUnseal :: Int
walletFull       = 6
itemDoesNotExist = 7
itemTooLong      = 8
failSeal         = 9
failUnseal       = 10

-- * Static values

maxItems :: Int
maxItems = 100

maxItemSize :: Int
maxItemSize = 100

wallet :: String
wallet = "wallet.seal"

-- * Data types

data Item = Item
    { title    :: String
    , username :: String
    , password :: String
    }
  deriving (Show, Read)

data Wallet = Wallet
    { items          :: [Item]
    , size           :: Int
    , masterPassword :: String
    }
  deriving (Show, Read)

newWallet :: Password -> Wallet
newWallet mp = Wallet [] 0 mp

type Password = String

-- * Enclave code

passwordPolicy :: Password -> Bool
passwordPolicy pass = length pass >= 8 && length pass + 1 <= maxItemSize

loadWallet :: Server (Maybe Wallet)
loadWallet = do
  b <- API.doesFileExist wallet
  unsafePrint (show b)
  if b
    then do contents <- API.readFile wallet
            return $ (readMaybe contents :: Maybe Wallet)
    else return Nothing

saveWallet :: Wallet -> Server ()
saveWallet w = API.writeFile wallet (show w)

createWallet :: Password -> Server Int
createWallet mp
  | not $ passwordPolicy mp = return passwordOutOfRange
  | otherwise = do
    w <- loadWallet
    case w of
        Just _  -> return walletAlreadyExists
        Nothing -> saveWallet (newWallet mp) >> return retSuccess

changeMasterPassword :: Password -> Password -> Server Int
changeMasterPassword old new
  | not $ passwordPolicy new = return passwordOutOfRange
  | otherwise = do
    w <- loadWallet
    case w of
      Nothing -> return cannotLoadWallet
      Just w -> if masterPassword w == old
                    then saveWallet (w { masterPassword = new }) >> return retSuccess
                    else return wrongMasterPassword

addItem :: Password -> String -> String -> Password -> Server Int
addItem mp item username pass
  | length item + 1     > maxItemSize ||
    length username + 1 > maxItemSize ||
    length pass + 1 > maxItemSize = return itemTooLong
  | otherwise = do
    w <- loadWallet
    case w of
        Nothing -> return cannotLoadWallet
        Just w ->
            if masterPassword w == mp
                -- FIXME check if item already exists
                then saveWallet (w { items = (Item item username pass) : items w, size = size w + 1}) >> return retSuccess
                else return wrongMasterPassword

removeItem :: Password -> String -> Server Int
removeItem mp item = do
  w <- loadWallet
  case w of
      Nothing -> return cannotLoadWallet
      Just w | not (item `elem` (map title (items w))) -> return itemDoesNotExist
      Just w | not (masterPassword w == mp) -> return wrongMasterPassword
      Just w -> saveWallet (w { items = filter (not . (==) item . title) (items w), size = size w - 1}) >> return retSuccess

-- * The application

data Api = Api
    { create     :: Remote (Password -> Server Int)
    , changePass :: Remote (Password -> Password -> Server Int)
    , add        :: Remote (Password -> String -> String -> Password -> Server Int)
    , remove     :: Remote (Password -> String -> Server Int)
    }

app :: App Done
app = do
    -- The api
    create     <- remote $ createWallet
    changePass <- remote $ changeMasterPassword
    add        <- remote $ addItem
    remove     <- remote $ removeItem

    -- Client code
    runClient $ clientApp $ Api create changePass add remove

data Command
    = Create
    | Change Password Password
    | Add String String Password
    | Remove String
    | Shutoff
  deriving Show

clientApp :: Api -> Client ()
clientApp api = do
    cmd <- getCommand
    case cmd of
        Shutoff -> liftIO (putStrLn "turning off...") >> return ()
        _       -> do liftIO $ hPutStr stdout "master password: "
                      liftIO $ hFlush stdout
                      mp <- liftIO $ getLine
                      r <- onServer $ case cmd of
                             Create                      -> create api <.> mp
                             Change old new              -> changePass api <.> old <.> new
                             Add title username password -> add api <.> mp <.> title <.> username <.> password
                             Remove title                -> remove api <.> mp <.> title
                      printCode r

getCommand :: Client Command
getCommand = do
    liftIO $ hPutStr stdout "> "
    liftIO $ hFlush stdout
    input <- liftIO $ getLine
    case input of
        [] -> getCommand
        s -> case tryParse s of
            Just c -> return c
            Nothing -> getCommand
  where
    tryParse :: String -> Maybe Command
    tryParse input = case words input of
        ["create"]                         -> Just Create
        ["change", old, new]               -> Just $ Change old new
        ["add", title, username, password] -> Just $ Add title username password
        ["remove", title]                  -> Just $ Remove title
        ["shutoff"]                        -> Just Shutoff
        otherwise                          -> Nothing

printCode :: Int -> Client ()
printCode c
  | c == retSuccess          = liftIO $ putStrLn $ "# ok"
  | c == passwordOutOfRange  = liftIO $ putStrLn $ "= password out of range"
  | c == walletAlreadyExists = liftIO $ putStrLn $ "= wallet already exists"
  | c == cannotSaveWallet    = liftIO $ putStrLn $ "= cannot save wallet"
  | c == cannotLoadWallet    = liftIO $ putStrLn $ "= cannot load wallet"
  | c == wrongMasterPassword = liftIO $ putStrLn $ "= wrong master password"
  | c == walletFull          = liftIO $ putStrLn $ "= wallet is full"
  | c == itemDoesNotExist    = liftIO $ putStrLn $ "= item does not exist"
  | c == itemTooLong         = liftIO $ putStrLn $ "= item is too long"
  | c == failSeal            = liftIO $ putStrLn $ "= failure while sealing wallet"
  | c == failUnseal          = liftIO $ putStrLn $ "= failure while unsealing wallet"

main :: IO ()
main = do
  res <- runApp app
  return $ res `seq` ()
