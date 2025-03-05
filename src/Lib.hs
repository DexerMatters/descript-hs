{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Lib where

import LSP (generateMessages)
import System.Environment (getArgs)

runTest :: () -> IO ()
runTest () = do
  args <- getArgs
  let code = case args of
        ["-t", x] -> x
        _ -> error "Usage: descript -t <code>"
  code' <- readFile "/home/dexer/Repos/haskell/descript-hs/demo/test.ds"
  LSP.generateMessages code
