{-# LANGUAGE LambdaCase #-}

module Program where

import           Syn
import           Utils
import           Data.Void (Void)
import           ElabUtils (ElabEnv, emptyEnv, typeBindings, bindings)

data ProgEnv = ProgEnv { typeDecl :: [(String, TypeTerm)]
                       , termDecl :: [(String, ExprTerm)]
                       }
  deriving (Show)

type ProgState = MState ProgEnv Void

