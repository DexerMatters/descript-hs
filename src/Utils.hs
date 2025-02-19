
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}

{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Utils where

import           Debug.Trace
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Maybe (fromMaybe)
import           GHC.Base (liftA2)
import           Control.Monad (when, unless)
import qualified Data.List as List
import           Data.Function (on)

-- | Auxiliary functions

type (|->) a b = [(a, b)]

type Ref = Int

type Level = Int

type Index = Int

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

-- | Array utilities

(!!!) :: Seq a -> Int -> a
s !!! i =
  fromMaybe (error $ "Index " ++ show i ++ " out of bounds") (s Seq.!? i)

(-|) :: a -> (a -> b) -> b
(-|) = flip ($)

infix 0 -|

lookupSS :: Seq (Seq a) -> (Int, Int) -> Maybe a
lookupSS s (i, j) = s Seq.!? i >>= (Seq.!? j)

pattern (:@:) :: a -> b -> (a, b)
pattern a :@: b = (a, b)

infixr 1 :@:

(@@) :: Monad m => m a -> m b -> m (a, b)
(@@) = liftA2 (,)

infixl 2 @@

whenM :: Monad m => m Bool -> m () -> m ()
whenM m f = m >>= flip when f

unlessM :: Monad m => m Bool -> m () -> m ()
unlessM m f = m >>= \b -> unless b f

nubAndSortBy :: (a -> a -> Ordering) -> [a] -> [a]
nubAndSortBy cmp = List.sortBy cmp . List.nubBy (\x y -> cmp x y == EQ)

nubAndSortAssoc :: Ord a => [(a, b)] -> [(a, b)]
nubAndSortAssoc = nubAndSortBy (compare `on` fst)

hashIntPair :: (Int, Int) -> Int
hashIntPair (x, y) = (x + y) * (x + y + 1) `div` 2 + y

