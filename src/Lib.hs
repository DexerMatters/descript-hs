module Lib where

import           Control.Monad.State (StateT(runStateT), State, MonadState(put)
                                    , MonadTrans(lift))
import           Control.Monad.State.Lazy (runState)
import           Text.Megaparsec (parseErrorPretty, runParser, parse
                                , errorBundlePretty)
import           Utils (fatal, success)
import           Parser (allowedAll)
import           TypeElab (testTypeCheck)

runTest :: () -> IO ()
runTest () = do
  -- Read the file
  raw <- readFile filePath
  case parse allowedAll "" raw of
    Left err  -> putStrLn . fatal $ errorBundlePretty err
    Right ast -> do
      case testTypeCheck ast of
        Left err -> putStrLn . fatal $ show err
        Right t  -> putStrLn . success $ show t
  where
    filePath = "/home/dexer/Repos/haskell/descript-hs/demo/test.ds"