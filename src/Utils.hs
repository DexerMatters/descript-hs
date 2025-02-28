
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}

{-# OPTIONS_GHC -Wno-missing-export-lists #-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}

module Utils where

import           Debug.Trace
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Maybe (fromMaybe)
import           GHC.Base (liftA2, maxInt)
import           Control.Monad (when, unless)
import qualified Data.List as List
import           Data.Function (on)

-- | Auxiliary functions

type (|->) a b = [(a, b)]

type Ref = Int

type Level = Int

type Index = Int

data FI = FI { start :: Int, end :: Int }
  deriving (Eq, Show)

instance Semigroup FI where
  FI s e <> FI s' e' = FI (min s s') (max e e')

instance Monoid FI where
  mempty = FI maxInt 0

data WithFI a = WithFI { fi :: FI, val :: a }
  deriving (Eq, Functor, Show, Foldable)

pattern (:?>) :: FI -> a -> WithFI a
pattern f :?> a = WithFI f a

infixl 5 :?>

instance Traversable WithFI where
  traverse f (i :?> a) = (i :?>) <$> f a
  traverse _ _ = error "Unreachable"

fiEmpty :: a -> WithFI a
fiEmpty = (FI maxInt 0 :?>)

data Border a = Border { top :: a, bot :: a }
  deriving (Functor)

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

zipWith' :: (Monoid a, Monoid b) => (a -> b -> c) -> Seq a -> Seq b -> Seq c
zipWith' f a b
  | Seq.length a > Seq.length b =
    Seq.zipWith f a (b <> Seq.replicate (Seq.length a - Seq.length b) mempty)
  | otherwise =
    Seq.zipWith f (a <> Seq.replicate (Seq.length b - Seq.length a) mempty) b

-- | Laziness

newtype Lazy b a = Lazy { force :: b -> a }

instance Functor (Lazy b) where
  fmap f (Lazy g) = Lazy (f . g)

instance Applicative (Lazy b) where
  pure = Lazy . const

  Lazy f <*> Lazy x = Lazy $ \b -> f b (x b)

instance Monad (Lazy b) where
  return = pure

  Lazy f >>= g = Lazy $ \b -> (force $ g (f b)) b

type ($) a b = a b

infixr 0 $