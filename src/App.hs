{-# LANGUAGE GeneralizedNewtypeDeriving, StaticPointers #-}


module App (module App) where

import Control.Monad.IO.Class
import Control.Monad.Trans.State.Strict

import Data.ByteString.Lazy(ByteString, append, length, fromStrict)
import Data.Binary(Binary, encode, decode)
import Data.Maybe(fromMaybe)
import Network.Simple.TCP

import Data.Dynamic

{-@ The EnclaveIFC API for programmers

-- use the below functions to describe your enclave API

-- mutable references
liftNewRef :: a -> App (Enclave (Ref a))
newRef :: a -> Enclave (Ref a)
readRef    :: Ref a -> Enclave a
writeRef   :: Ref a -> a -> Enclave ()
-- immutable value
inEnclaveConstant :: a -> App (Enclave a)
-- closures
-- create an escape hatch that can be used however many times you want
inEnclave :: Securable a => a -> App (Secure a)

-- create an escape hatch that can be used only a specific amount of times
ntimes :: Securable a => Int -> a -> App (Secure a)

-- use the below function to introduce the Client monad
runClient :: Client a -> App Done


-- use the 3 functions below to talk to the enclave
-- inside the Client monad

-- try to extract a result from a enclave computation. Might fail if the
-- declassifier does not allow the information leak
tryEnclave :: Secure (Enclave a) -> Client (Maybe a)

-- Extract a result from a enclave computation, with the assumption
-- that it will not fail. Will throw an exception if the result is not
-- returned due to some policy violation.
gateway :: Secure (Enclave a) -> Client a
(<@>) :: Binary a => Secure (a -> b) -> a -> Secure b

-- call this from `main` to run the App monad
runApp :: App a -> IO a


@-}


type Identifier = String
type CallID = Int
type Method = [ByteString] -> IO (Maybe ByteString)
type AppState = (CallID, [(CallID, Method)], Identifier)
newtype App a = App (StateT AppState IO a)
  deriving (Functor, Applicative, Monad, MonadIO)

data Done = Done

initAppState :: Identifier -> AppState
initAppState str = (0,[], str)

-- Client-enclave communication utils follow

localhost :: String
localhost = "127.0.0.1"

connectPort :: String
connectPort = "8000"

{-@ `createPayload` creates the  binary request to send over TCP.

     The payload comprise of:
     8 bytes message length followed by n bytes message body
     where n :: Int64 (from the length function in `bytestring`)

@-}
createPayload :: Binary a => a -> ByteString
createPayload msg = append bytstr msgBody
  where
    msgBody = encode msg
    msgSize = Data.ByteString.Lazy.length msgBody
    bytstr  = encode msgSize

readTCPSocket :: (MonadIO m) => Socket -> m ByteString
readTCPSocket socket = do
  -- first 8 bytes (Int64) encodes the msg size
  mSize <- recv socket 8
  let mSize_ = fromMaybe err mSize
  -- read the actual message body now
  msgBody <- recv socket (decode $ fromStrict mSize_)
  return $ fromStrict $ fromMaybe err msgBody
  where
    err = error "Error parsing request"


-- Introducing labels

class (Eq l, Show l, Read l, Typeable l) => Label l where
  lub       :: l -> l -> l
  glb       :: l -> l -> l
  canFlowTo :: l -> l -> Bool

infixl 5 `lub`, `glb`
infix 4 `canFlowTo`

data HierarchicalLabels = H -- high
                        | L -- low
                        deriving (Eq, Show, Read, Typeable)

instance Label HierarchicalLabels where
  canFlowTo L H = True
  canFlowTo L L = True
  canFlowTo H H = True
  canFlowTo H L = False

  lub H L = H
  lub L H = H
  lub L L = L
  lub H H = H

  glb H L = L
  glb L H = L
  glb H H = H
  glb L L = L

-- | Internal state of an 'LIO' computation.
data LIOState l = LIOState { lioLabel     :: !l -- ^ Current label.
                           , lioClearance :: !l -- ^ Current clearance.
                           } deriving (Eq, Show, Read, Typeable)
