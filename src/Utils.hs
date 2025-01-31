{-# LANGUAGE TypeOperators #-}

module Utils where

import           Debug.Trace
import           Data.Map (Map)

-- | Auxiliary functions

type (|->) a b = Map a b

type Ref = Int

-- | Implementation for debugging purposes

tr :: Show a => a -> a
tr x = trace ("[TRACE] " ++ show x) x

-- | Colorful output

warn :: String -> String
warn s = "\x1b[33m" ++ s ++ "\x1b[0m"

fatal :: String -> String
fatal s = "\x1b[31m" ++ s ++ "\x1b[0m"

info :: String -> String
info s = "\x1b[34m" ++ s ++ "\x1b[0m"

success :: String -> String
success s = "\x1b[32m" ++ s ++ "\x1b[0m"

trival :: String -> String
trival s = "\x1b[36m" ++ s ++ "\x1b[0m"

-- | Monads
