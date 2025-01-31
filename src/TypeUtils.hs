{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DuplicateRecordFields #-}

module TypeUtils where

import           Utils (Ref, type (|->))
import           Syn (TypeTerm)
import           Control.Monad.State (StateT)
import           Control.Monad.Except (ExceptT)

-- Environment for type checking


newtype TypeElabEnv = TypeElabEnv { bindings :: String |-> TypeTerm }

newtype TypeEvalEnv = TypeEvalEnv { bindings :: Ref |-> TypeTerm }

data TypeError = UndefinedType String
               | TypeMismatch TypeTerm TypeTerm

-- Monad for type checking
