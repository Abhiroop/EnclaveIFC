{-# LANGUAGE CPP #-}
module Main where

import Control.Monad.IO.Class(liftIO)

import App

#ifdef ENCLAVE
import Enclave
#else
import Client
#endif
 
pwdChkr :: Enclave String -> String -> Enclave Bool
pwdChkr pwd guess = fmap (== guess) pwd


passwordChecker :: App Done
passwordChecker = do
  paswd <- inEnclaveConstant ("secret") :: App (Enclave String) -- see NOTE 1
  enclaveFunc <- inEnclave $ pwdChkr paswd
  runClient $ do
    liftIO $ putStrLn "Enter your password"
    userInput <- liftIO getLine
    res <- gateway (enclaveFunc <@> userInput)
    liftIO $ putStrLn $ "Your login attempt returned " <> (show res)


main :: IO ()
main = do
  putStrLn "before"
  res <- runApp passwordChecker
  putStrLn "after"
  return $ res `seq` ()
