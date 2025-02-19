{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Lib where

import           Text.Megaparsec (parse, errorBundlePretty)
import           Utils (fatal)
import           Parser (allowedAll)
import           TypeElab (testTypeCheck)
import           Pretty (render, PrettyPrint(pretty))

runTest :: () -> IO ()
runTest () = do
  -- Read the file
  raw <- readFile filePath
  case parse allowedAll "" raw of
    Left err  -> putStrLn . fatal $ errorBundlePretty err
    Right ast -> do
      case testTypeCheck ast of
        Left err -> putStrLn . fatal $ show err
        Right t  -> putStrLn $ render $ pretty t
  where
    filePath = "/home/dexer/Repos/haskell/descript-hs/demo/test.ds"