
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Pretty where

import           Control.Monad.State (State, evalState, modify, gets)
import           Data.Set (Set)
import qualified Data.Set as Set

data Pretty b a = Show a => Text a
                | Concat (Pretty b a) (Pretty b a)
                | Indent Int (Pretty b a)
                | Colored Color (Pretty b a)
                | Newline
                | Ord b => Fresh (Int -> Pretty b a) b
                | Empty

data Color =
    Red
  | Green
  | Blue
  | Yellow
  | Magenta
  | Cyan
  | White
  | BrightRed
  | BrightGreen
  | BrightBlue
  | BrightYellow
  | BrightMagenta
  | BrightCyan
  | Bold Color
  | Italics Color
  | Dim Color

type family RawString t

newtype RawStr = RawStr String

type instance RawString String = RawStr

instance Show Color where
  show = \case
    Red           -> "31"
    Green         -> "32"
    Blue          -> "34"
    Yellow        -> "33"
    Magenta       -> "35"
    Cyan          -> "36"
    White         -> "37"
    BrightRed     -> "91"
    BrightGreen   -> "92"
    BrightBlue    -> "94"
    BrightYellow  -> "93"
    BrightMagenta -> "95"
    BrightCyan    -> "96"
    Bold c        -> "1;" ++ show c
    Italics c     -> "3;" ++ show c
    Dim c         -> "2;" ++ show c

txt :: String -> Pretty b RawStr
txt = Text . RawStr

space :: Pretty b RawStr
space = txt " "

freshAlphabet :: Ord b => b -> Pretty b RawStr
freshAlphabet = Fresh $ \i -> txt (['a' .. 'z'] !! i:"")

freshGreek :: Ord b => b -> Pretty b RawStr
freshGreek = Fresh $ \i -> txt (['α' .. 'ω'] !! i:"")

( #> ) :: Color -> Pretty b a -> Pretty b a
( #> ) = Colored

infixr 9 #>

concat :: Foldable t => t (Pretty b a) -> Pretty b a
concat = foldr Concat Empty

concatWith :: Foldable t => Pretty b a -> t (Pretty b a) -> Pretty b a
concatWith divider = foldr1
  $ curry
  $ \case
    (a, Empty) -> a
    (a, b)     -> Concat a (Concat divider b)

render :: Ord b => Pretty b a -> String
render x = evalState (render' 0 [] x) Set.empty

render' :: Ord s => Int -> [Color] -> Pretty s a -> State (Set s) String
render' i cs = fmap ((replicate i ' ' <> colorNow cs ++) . (++ colorAfter cs))
  . (\case
       Text a      -> pure $ show a
       Concat a b  -> (++) <$> render' i cs a <*> render' i cs b
       Indent n p  -> render' (i + n) cs p
       Colored c p -> render' i (c:cs) p
       Newline     -> pure "\n"
       Fresh f b   -> gets (Set.lookupIndex b)
         >>= \case
           Just j  -> render' i cs $ f j
           Nothing -> do
             j <- gets Set.size
             modify (Set.insert b)
             render' i cs $ f j
       Empty       -> pure "")
  where
    colorNow [] = ""
    colorNow (c:_) = "\x1b[" ++ show c ++ "m"

    colorAfter [] = ""
    colorAfter [_] = "\x1b[0m"
    colorAfter (_:c:_) = "\x1b[" ++ show c ++ "m"

instance Semigroup (Pretty b a) where
  Empty <> p = p
  p <> Empty = p
  p <> q = Concat p q

instance Monoid (Pretty b a) where
  mempty = Empty

instance Show RawStr where
  show (RawStr s) = s

class PrettyPrint a where
  pretty :: a -> Pretty Int RawStr