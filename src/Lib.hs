{-# OPTIONS_GHC -Wno-missing-export-lists #-}

{-# LANGUAGE MultiParamTypeClasses #-}

module Lib where

import           Text.Megaparsec (parse, errorBundlePretty)
import           Utils (fatal)
import           Parser (allowedAll)
import           Pretty (render)
import           TypePretty (testInferType)
import           System.IO

runTest :: () -> IO ()
runTest () = do
  -- hSetBuffering stdout NoBuffering
  -- putStr "> "
  -- raw <- getLine
  -- case parse allowedAll "" raw of
  --   Left err  -> putStrLn . fatal $ errorBundlePretty err
  --   Right ast -> do
  --     case testInferType ast of
  --       Left err   -> putStrLn . fatal $ show err
  --       Right ptty -> putStrLn $ render ptty
  -- runTest ()


  -- Read the file
  raw <- readFile filePath
  case parse allowedAll "" raw of
    Left err  -> putStrLn . fatal $ errorBundlePretty err
    Right ast -> do
      case testInferType ast of
        Left err   -> putStrLn . fatal $ show err
        Right ptty -> putStrLn $ render ptty
  where
    filePath = "/home/dexer/Repos/haskell/descript-hs/demo/test.ds"

