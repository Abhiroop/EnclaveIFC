module Main (main) where

import Control.Monad.IO.Class
import Data.IORef

import Lib
import Client
--import Server


app :: App Done
app = do
  remoteRef <- liftServerIO (newIORef 0) :: App (Server (IORef Int))
  count <- remote $ do
    r <- remoteRef
    liftIO $ atomicModifyIORef r (\v -> (v+1, v+1))
  runClient $ do
    visitors <- onServer count
    liftIO $ putStrLn $ "You are visitor number #" ++ show visitors


main :: IO ()
main = do
  res <- runApp app
  return $ res `seq` ()
