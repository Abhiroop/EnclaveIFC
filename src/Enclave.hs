{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ScopedTypeVariables, RankNTypes, TypeApplications #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
module Enclave(module Enclave) where

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.State.Strict
import Data.Binary(Binary, encode, decode)
import Data.ByteString.Lazy(ByteString)
import Data.IORef
import Data.Maybe
import Network.Simple.TCP
import System.IO(hFlush, stdout)
import App

import qualified Data.ByteString.Lazy as B

type Ref a = IORef a
newtype Enclave a = Enclave (IO a)

instance Functor (Enclave) where
  fmap f (Enclave x) = Enclave $ fmap f x

instance Applicative Enclave where
  pure x = Enclave (pure x)
  Enclave f <*> Enclave a = Enclave $ f <*> a

instance Monad Enclave where
  return = pure
  Enclave ma >>= k = Enclave $ do
    a <- ma
    let Enclave ka = k a
    ka


data Secure a = SecureDummy

inEnclaveConstant :: a -> App (Enclave a)
inEnclaveConstant = return . return

liftNewRef :: a -> App (Enclave (Ref a))
liftNewRef a = App $ do
  r <- liftIO $ newIORef a
  return (return r)

newRef :: a -> Enclave (Ref a)
newRef x = Enclave $ newIORef x

readRef :: Ref a -> Enclave a
readRef ref = Enclave $ readIORef ref

writeRef :: Ref a -> a -> Enclave ()
writeRef ref v = Enclave $ writeIORef ref v

inEnclave :: (Securable a) => a -> App (Secure a)
inEnclave f = App $ do
  (next_id, remotes) <- get
  put (next_id + 1, (next_id, \bs -> let Enclave n = mkSecure f bs in n) : remotes)
  return SecureDummy

ntimes :: (Securable a) => Int -> a -> App (Secure a)
ntimes n f = App $ do
  r <- liftIO $ newIORef n
  (next_id, remotes) <- get
  put (next_id + 1, (next_id, \bs ->
    let Enclave s = do
          c <- Enclave $ do atomicModifyIORef' r $ \i -> (i - 1, i)
          if c > 0
          then mkSecure f bs
          else return Nothing
    in s) : remotes)


  return SecureDummy

(<@>) :: Binary a => Secure (a -> b) -> a -> Secure b
(<@>) = error "Access to client not allowed"


class Securable a where
  mkSecure :: a -> ([ByteString] -> Enclave (Maybe ByteString))

instance (Binary a) => Securable (Enclave a) where
  mkSecure m = \_ -> fmap (Just . encode) m

instance (Binary a, Securable b) => Securable (a -> b) where
  mkSecure f = \(x:xs) -> mkSecure (f $ decode x) xs

data Client a = ClientDummy deriving (Functor, Applicative, Monad, MonadIO)

runClient :: Client a -> App Done
runClient _ = return Done

tryEnclave :: (Binary a) => Secure (Enclave a) -> Client (Maybe a)
tryEnclave _ = ClientDummy

gateway :: Binary a => Secure (Enclave a) -> Client a
gateway _ = ClientDummy

unsafeOnEnclave :: Binary a => Secure (Enclave a) -> Client a
unsafeOnEnclave _ = ClientDummy

{-@ The enclave's event loop. @-}
runApp :: App a -> IO a
runApp (App s) = do
  (a, (_, vTable)) <- runStateT s initAppState
  {- BLOCKING HERE -}
  _ <- serve (Host localhost) connectPort $
    \(connectionSocket, remoteAddr) -> do
      -- debug log
      putStrLn $ "TCP connection established from " ++ show remoteAddr
      hFlush stdout -- Gramine prints only if stdout is flushed
      req <- readTCPSocket connectionSocket
      onEvent vTable req connectionSocket
  {- BLOCKING ENDS -}
  return a -- the a is irrelevant



onEvent :: [(CallID, Method)] -> ByteString -> Socket -> IO ()
onEvent mapping incoming socket = do
  let (identifier, args) = decode incoming :: (CallID, [ByteString])
      Just f = lookup identifier mapping
  result <- encode <$> f args
  let res = handleVoidTy result -- the () type cannot be sent over wire
  sendLazy socket (B.append (msgSize res) res) -- See NOTE 1
  where
    msgSize r = encode $ B.length r
    handleVoidTy r = if (B.length r == 0) -- the () type has msg length 0
                     then encode '\0'
                     else r

-- NOTE 1
-- We do not use `createPayload` because as a first step it
-- encodes the message body to a ByteString. In case of the
-- enclave the `result` is already a ByteString. So it further
-- encodes the ByteString and gives a wrong result.
-- We can modify the `createPayload` function so that depending
-- on the value of some identifier term that we send, it decides
-- to encode or not encode the message body but then the type
-- will become an actual dependent type. (Keep it simple!)

