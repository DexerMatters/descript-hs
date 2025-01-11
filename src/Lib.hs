module Lib (runTest) where

import           Utils (MState(..), put)
import           Text.Megaparsec (parse, parseTest, errorBundlePretty)
import           Parser (allowedAll, parseProj)
import           Elab (elaborate, ElabResult(ety))
import           ElabUtils (emptyEnv)
import           EvalT
import           EvalTUtils

path :: String
path = "/home/dexer/Repos/haskell/descript-hs/demo/test.ds"

runTest :: () -> IO ()
runTest _ = do
  -- Read the file
  content <- readFile path
  -- Parse the file
  let parsed = parse allowedAll path content
  case parsed of
    Left e  -> putStrLn $ errorBundlePretty e
    Right r -> do
      putStrLn "Parsed Result:"
      print r
      case runMState (elaborate r) emptyEnv of
        Left e         -> print e
        Right (a, env) -> do
          putStrLn "Elaborated Result:"
          print (ety a)
          putStrLn "Elaborated Environment:"
          print env
          putStrLn "Type of the expression:"
          case runMState (evalT (ety a) >>= pretty) (fromElabEnv env) of
            Left e        -> print e
            Right (a', _) -> putStrLn a'