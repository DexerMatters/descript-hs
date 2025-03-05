{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module TypePretty where

import Pretty
  ( Pretty,
    PrettyPrint (..),
    RawStr,
    concatWith,
    freshGreek,
    txt,
  )
import Syn
  ( PrimitiveType,
    TypeDescriptor,
  )
import Utils
  ( Index,
    Level,
    pattern (:?>),
  )
import qualified Utils as U

data TypePtty
  = PttyPrimitive PrimitiveType
  | PttyLam [((Level, Index, String), BorderPtty)] TypePtty'
  | PttyVar BorderPtty TypeDescriptor Level Index
  | PttyTop
  | PttyBot
  | PttyArrow [TypePtty'] TypePtty'
  | PttyTuple [TypePtty']
  | PttyRecord [(String, TypePtty')]
  deriving (Show)

type TypePtty' = U.WithFI TypePtty

type BorderPtty = U.Border TypePtty'

instance Show BorderPtty where
  show (U.Border t b) = show b ++ "~" ++ show t

instance PrettyPrint BorderPtty (Int, Int) where
  pretty (U.Border (_ :?> PttyBot) (_ :?> PttyTop)) = txt "∅"
  pretty (U.Border t b) = pretty b <> txt "~" <> pretty t

pretty0 :: TypePtty' -> Pretty (Int, Int) RawStr
pretty0 t@(U.FI "" _ _ U.:?> (PttyVar border _ _ _)) =
  pretty t <> txt ": " <> pretty border
pretty0 t = pretty t

instance PrettyPrint TypePtty' (Int, Int) where
  pretty :: TypePtty' -> Pretty (Int, Int) RawStr
  pretty (_ :?> PttyPrimitive pt) = txt $ show pt
  pretty (U.FI "" _ _ U.:?> PttyVar _ _ lvl idx) = freshGreek (lvl, idx)
  pretty (U.FI x _ _ U.:?> PttyVar {}) = txt x
  pretty (_ :?> PttyTop) = txt "⊤"
  pretty (_ :?> PttyBot) = txt "⊥"
  pretty (_ :?> PttyArrow args ret) =
    txt "("
      <> concatWith (txt ", ") (pretty <$> args)
      <> txt ") -> "
      <> pretty ret
  pretty (_ :?> PttyTuple elems) =
    txt "(" <> concatWith (txt ", ") (pretty <$> elems) <> txt ")"
  pretty (_ :?> PttyRecord fields) =
    txt "{" <> concatWith (txt ", ") parseFields <> txt "}"
    where
      parseFields = (\(l, t) -> txt l <> txt ": " <> pretty t) <$> fields
  pretty (_ :?> PttyLam vars body) =
    txt "forall "
      <> concatWith (txt ", ") parseBorders
      <> txt ". "
      <> pretty body
    where
      parseBorders =
        flip map vars $ \(v, b) -> parseVar v <> txt ": " <> pretty b

      parseVar (lvl, idx, "") = freshGreek (lvl, idx)
      parseVar (_, _, x) = txt x
  pretty _ = error "This should never happen"

pretty' :: TypePtty' -> Pretty (Int, Int) RawStr
pretty' = pretty
