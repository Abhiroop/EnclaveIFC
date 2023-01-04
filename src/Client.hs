{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
module Client(module Client) where

import Control.Monad.IO.Class
import Control.Monad.Trans.State.Strict
import Data.ByteString.Lazy(ByteString)
import Data.Binary(Binary, encode, decode)
import Network.Simple.TCP
import App

data Ref a = RefDummy
data Server a = ServerDummy deriving (Functor, Applicative, Monad)
data Remote a = Remote CallID [ByteString]

(<.>) :: Binary a => Remote (a -> b) -> a -> Remote b
(Remote identifier args) <.> arg =
  Remote identifier (encode arg : args)

{- The Remotable a constraint is necessary for the Server type -}
remote :: (Remotable a) => a -> App (Remote a)
remote _ = App $ do
  (next_id, remotes) <- get
  put (next_id + 1, remotes)
  return $ Remote next_id []

class Remotable a where
  mkRemote :: a -> ([ByteString] -> Server ByteString)

instance (Binary a) => Remotable (Server a) where
  mkRemote m = \_ -> fmap encode m

instance (Binary a, Remotable b) => Remotable (a -> b) where
  mkRemote f = \(x:xs) -> mkRemote (f $ decode x) xs

serverConstant :: a -> App (Server a)
serverConstant _ = return ServerDummy

liftNewRef :: a -> App (Ref a)
liftNewRef _ = return RefDummy

newRef :: a -> Server (Ref a)
newRef _ = ServerDummy

readRef :: Ref a -> Server a
readRef _ = ServerDummy

writeRef :: Ref a -> a -> Server ()
writeRef _ _ = ServerDummy


type Client = IO


runClient :: Client a -> App Done
runClient cl = do
  v <- liftIO cl
  return $ v `seq` Done

onServer :: (Binary a) => Remote (Server a) -> Client a
onServer (Remote identifier args) = do
  {- SENDING REQUEST HERE -}
  connect localhost connectPort $ \(connectionSocket, remoteAddr) -> do
    -- debug logs
    putStrLn $ "Connection established to " ++ show remoteAddr
    sendLazy connectionSocket $ createPayload (identifier, reverse args)
    resp <- readTCPSocket connectionSocket
    return $ decode resp
  {- SENDING ENDS -}

ntimes :: Binary a => Int -> (Remote (Server a) -> Client a) -> App (Remote (Server a) -> Client (Maybe a))
ntimes n h = do
  r <- liftNewRef n
  check <- remote $ do
    v <- readRef r
    writeRef r $ v - 1
    return (v > 0)
  return $ \sa -> do
    c <- onServer check
    if c
      then Just <$> h sa
      else return Nothing

runApp :: App a -> IO a
runApp (App s) = evalStateT s initAppState
