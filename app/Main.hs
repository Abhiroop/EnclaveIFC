{-# LANGUAGE CPP #-}

{-# LANGUAGE DataKinds #-}
module Main where

import Data.Binary
import Data.Bits (shift, (.|.))
import Data.Word (Word8)
import Foreign.C
import Foreign.C.Types
import Foreign.Ptr
import Foreign.Storable (peekElemOff)
import qualified Data.ByteString as B


-- import Control.Monad.IO.Class(liftIO)
-- import Data.List(genericLength)
-- import GHC.Float(int2Float)
-- import App
-- import Security.Sec

-- #ifdef ENCLAVE
-- import Enclave
-- #else
-- import Client
-- #endif



-- getData :: Enclave (Ref (Sec [Int])) -> Int -> Enclave Int
-- getData serv_secret idx = do
--   secret <- serv_secret
--   sech <- readRef secret
--   let sec_i = fmap (\s -> s !! idx) sech
--   return (declassify sec_i)

-- releaseAvg :: Enclave (Ref Bool) -> Enclave ()
-- releaseAvg sbool = do
--   bool <- sbool
--   writeRef bool True

-- doAvg :: [Int] -> Float
-- doAvg xs = realToFrac (sum xs) / genericLength xs

-- getAvg :: Enclave (Ref Bool) -> Enclave (Ref (Sec [Int])) -> Enclave Float
-- getAvg serv_bool serv_secret = do
--   bool   <- serv_bool
--   secret <- serv_secret
--   b <- readRef bool
--   if b
--   then do
--     s <- readRef secret
--     let s' = declassify s
--     let avg = doAvg s'
--     return avg
--   else return 0.0


-- printCl :: String -> Client ()
-- printCl = liftIO . putStrLn

-- app :: App Done
-- app = do
--   remoteSec1 <- liftNewRef (sec [15,30,11,6]) :: App (Enclave (Ref (Sec [Int])))
--   remoteSec2 <- liftNewRef False :: App (Enclave (Ref Bool))
--   gD <- inEnclave $ getData remoteSec1
--   rA <- inEnclave $ releaseAvg remoteSec2
--   gA <- inEnclave $ getAvg remoteSec2 remoteSec1
--   runClient $ do
--     data1 <- gateway (gD <@> 3)
--     _     <- gateway rA
--     avg   <- gateway gA
--     let b = dummyCompOnData data1 avg
--     printCl $ "Is data less than avg? " <> show b
--   where
--     dummyCompOnData i av = int2Float i < av


-- main :: IO ()
-- main = do
--   res <- runApp app
--   return $ res `seq` ()




import Control.Monad.IO.Class(liftIO)

import App

#ifdef ENCLAVE
import Enclave
#else
import Client
#endif

dataTillNow :: [Int]
dataTillNow = []

computeAvg :: Enclave (Ref [Int]) -> Enclave Int
computeAvg enc_ref_ints = do
  ref_ints <- enc_ref_ints
  vals     <- readRef ref_ints
  return (avg vals)
  where
    avg datas
      | (length datas) == 0 = 0
      | otherwise = sum datas `div` (length datas)

sendData :: Enclave (Ref [Int]) -> Int -> Enclave ()
sendData enc_ref_ints n = do
  ref_ints <- enc_ref_ints
  vals     <- readRef ref_ints
  writeRef ref_ints (n : vals)

data API =
  API { sendToEnclave :: Secure (Int -> Enclave ())
      , compAvg       :: Secure (Enclave Int)
      }





client1 :: API -> Client "client1" ()
client1 api = do
  gateway ((sendToEnclave api) <@> 50)
  res <- gateway (compAvg api)
  liftIO $ putStrLn $ "Computed result " <> (show res)

client2 :: API -> Client "client2" ()
client2 api = do
  gateway ((sendToEnclave api) <@> 70)
  res <- gateway (compAvg api)
  liftIO $ putStrLn $ "Computed result " <> (show res)

privateAverage :: App Done
privateAverage = do
  initialData <- liftNewRef dataTillNow
  sD <- inEnclave $ sendData initialData
  cA <- inEnclave $ computeAvg initialData
  runClient "client2" (client2 (API sD cA))

-- main :: IO ()
-- main = do
--   res <- runApp privateAverage
--   return $ res `seq` ()


foreign import ccall "exp" c_exp :: Double -> Double
foreign import ccall "add" c_add :: CInt -> CInt -> IO CInt
foreign import ccall "processByteArray" processByteArray
    :: Ptr CChar -> CSize -> IO (Ptr CChar)
foreign import ccall "processByteArrayDyn" processByteArrayDyn
    :: Ptr CChar -> IO (Ptr CChar)
foreign import ccall "stdlib.h free" c_free :: Ptr CChar -> IO ()


-- XXX: not portable;
-- 8 bytes for this machine
-- LSB/MSB order for this machine
byteStrLength :: Ptr CChar -> IO Int
byteStrLength cptr = go 0 []
  where
    go 8 xs = do
      let (i0:i1:i2:i3:i4:i5:i6:i7:_) = xs
      let y = (shift i0 56) .|. (shift i1 48) .|. (shift i2 40) .|.
              (shift i3 32) .|. (shift i4 24) .|. (shift i5 16) .|.
              (shift i6  8) .|. i7
      return y
    go i xs = do
      cchar <- peekElemOff cptr i
      go (i + 1) ((fromEnum cchar):xs)

data Foo = A Int | B Bool deriving (Show, Eq)


instance Binary Foo where
  put (A i) = do
    put (0 :: Word8)
    put i
  put (B b) = do
    put (1 :: Word8)
    put b

  get = do
    t <- get :: Get Word8
    case t of
      0 -> do
        i <- get
        return (A i)
      1 -> do
        b  <- get
        return (B b)

foo = A 3
bar = B True

baz :: [Foo]
baz = [foo, bar]

main :: IO ()
main = do
  putStrLn $ show $ c_exp 2
  res <- c_add 5 3
  putStrLn $ "Haskell : " <> show res
  -- let inputBytes = B.pack [1, 2, 3, 4, 11]
  {- Binary's encode is interesting
     It uses 1 word to store the length of the data about to come
     1 word is 8 bytes in this machine;
     Hence its encode is platform dependent
  -}
  let inputBytes = B.toStrict $ encode baz
  B.useAsCStringLen inputBytes $ \(ptr, len) -> do
    cByteStr <- processByteArray ptr (fromIntegral len)
    putStrLn "Haskell Land"
    l <- byteStrLength cByteStr
    byteString <- B.packCStringLen (cByteStr `plusPtr` 8, l) -- XXX: not portable 8 bytes for this machine
    c_free cByteStr
    let result = decode (B.fromStrict byteString) :: [Foo]
    putStrLn $ "Hs to C and back : " <> (show result)

  -- B.useAsCString inputBytes $ \ptr -> do
  --   cByteStr   <- processByteArrayDyn ptr
  --   putStrLn "Haskell Land"
  --   byteString <- B.packCStringLen (cByteStr, 19)
  --   let result = decode (B.fromStrict byteString) :: [Foo]
  --   putStrLn $ "Hs to C and back : " <> (show result)

{- LINEAR HASKELL primer

{-# LANGUAGE LinearTypes #-}

import Prelude.Linear

g :: (a %1-> b) -> a -> b
g f x = body -- f can be used at most once in the body
  where
   body = f x

-}
