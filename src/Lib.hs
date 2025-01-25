module Lib (runTest) where

import           Text.Megaparsec (parse, errorBundlePretty)
import           Parser (parseProgram)
import           Typing (runTyping)

path :: String
path = "/home/dexer/Repos/haskell/descript-hs/demo/test.ds"

runTest :: () -> IO ()
runTest _ = do
  -- Read the file
  content <- readFile path
  -- Parse the file
  let parsed = parse parseProgram path content
  case parsed of
    Left e  -> putStrLn $ errorBundlePretty e
    Right r -> do
      putStrLn "Parsed Result:"
      print r
      putStrLn "Typechecking Result:"
      print $ runTyping r