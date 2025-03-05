{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Utils where

import Control.Monad (unless, when)
import Data.Data (Data, Typeable)
import Data.Function (on)
import qualified Data.List as List
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Debug.Trace
import GHC.Base (liftA2, maxInt)

-- | Auxiliary functions
type (|->) a b = [(a, b)]

type Ref = Int

type Level = Int

type Index = Int

data FI = FI String Int Int
  deriving (Eq, Show)

instance Semigroup FI where
  FI x s e <> FI x' s' e' = FI x' (min s s') (max e e')

instance Monoid FI where
  mempty = FI "" maxInt 0

data WithFI a = WithFI {fi :: FI, val :: a}
  deriving (Eq, Functor, Foldable)

instance (Show a) => Show (WithFI a) where
  show (WithFI _ a) = show a

pattern (:?>) :: FI -> a -> WithFI a
pattern f :?> a = WithFI f a

infixl 5 :?>

named :: FI -> String -> FI
named (FI _ s e) n = FI n s e

instance Traversable WithFI where
  traverse f (i :?> a) = (i :?>) <$> f a
  traverse _ _ = error "Unreachable"

fiEmpty :: a -> WithFI a
fiEmpty = (FI "" maxInt 0 :?>)

instance Ord FI where
  compare (FI _ s e) (FI _ s' e') = compare (e - s) (e' - s')

data Border a = Border {top :: a, bot :: a}
  deriving (Functor)

-- | Implementation for debugging purposes
tr :: (Show a) => a -> a
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

(.=) :: a -> b -> (a, b)
(.=) = (,)

(@@) :: (Monad m) => m a -> m b -> m (a, b)
(@@) = liftA2 (,)

infixl 2 @@

whenM :: (Monad m) => m Bool -> m () -> m ()
whenM m f = m >>= flip when f

unlessM :: (Monad m) => m Bool -> m () -> m ()
unlessM m f = m >>= \b -> unless b f

nubAndSortBy :: (a -> a -> Ordering) -> [a] -> [a]
nubAndSortBy cmp = List.sortBy cmp . List.nubBy (\x y -> cmp x y == EQ)

nubAndSortAssoc :: (Ord a) => [(a, b)] -> [(a, b)]
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
newtype Lazy b a = Lazy {force :: b -> a}

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

-- String formatting

class Formatable a where
  format :: a -> String

instance Formatable String where
  format = id

instance Formatable Char where
  format = pure

(+|) :: (Formatable a) => String -> a -> String
s +| a = s ++ format a

infixl 5 +|

(|+) :: (Formatable a) => a -> String -> String
a |+ s = format a ++ s

infixl 5 |+

(<+) :: (Monoid a, Monad m) => a -> m a -> m a
a <+ b = b >>= \b' -> pure $ a <> b'

infixl 5 <+

(+>) :: (Monoid a, Monad m) => m a -> a -> m a
a +> b = a >>= \a' -> pure $ a' <> b

infixl 5 +>

(<+>) :: (Monoid a, Monad m) => a -> a -> m a
a <+> b = pure $ a <> b

infixl 5 <+>

(<<>>) :: (Monoid a, Monad m) => m a -> m a -> m a
a <<>> b = a >>= \a' -> b >>= \b' -> pure $ a' <> b'

infixl 4 <<>>

-- Diagnostic utilities

class PartialOrder a where
  compare' :: a -> a -> Maybe Ordering
  (==?) :: a -> a -> Bool
  (==?) x y = compare' x y == Just EQ

  (/=?) :: a -> a -> Bool
  (/=?) x y = compare' x y /= Just EQ

  (<=?) :: a -> a -> Bool
  (<=?) x y = compare' x y == Just LT || compare' x y == Just EQ

  (>=?) :: a -> a -> Bool
  (>=?) x y = compare' x y == Just GT || compare' x y == Just EQ

  (<?) :: a -> a -> Bool
  (<?) x y = compare' x y == Just LT

  (>?) :: a -> a -> Bool
  (>?) x y = compare' x y == Just GT

data Range = Range {start :: Int, end :: Int}
  deriving (Show, Data, Typeable)

instance Semigroup Range where
  Range s1 e1 <> Range s2 e2 = Range (min s1 s2) (max e1 e2)

instance Monoid Range where
  mempty = Range maxInt 0

instance PartialOrder Range where
  compare' (Range s1 e1) (Range s2 e2)
    | s1 == s2 && e1 == e2 = Just EQ
    | s1 >= s2 && e1 <= e2 = Just LT
    | s1 <= s2 && e1 >= e2 = Just GT
    | otherwise = Nothing

-- Misc utilities

greekList :: [String]
greekList =
  [ "α",
    "β",
    "γ",
    "δ",
    "ε",
    "ζ",
    "η",
    "θ",
    "ι",
    "κ",
    "λ",
    "μ",
    "ν",
    "ξ",
    "ο",
    "π",
    "ρ",
    "σ",
    "τ",
    "υ",
    "φ",
    "χ",
    "ψ",
    "ω"
  ]