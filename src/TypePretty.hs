{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module TypePretty where

import           Syn (PrimitiveType, ExprTerm)
import           Utils (Level, Index, (!!!), tr)
import           TypeUtils (TypeValue(..), TypeCheckT, Border, TypeFailure)
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Control.Arrow (second)
import qualified Utils as U
import           Data.Foldable (foldrM)
import           Control.Monad (foldM)
import           TypeElab (botmost, elaborate, topmost)
import           Control.Monad.State (get, evalState)
import           Control.Monad.State.Lazy (gets)
import           Control.Monad.Except (runExceptT)
import           Data.Maybe (fromJust)
import           Pretty (Pretty, PrettyPrint(..), txt
                       , Color(Italics, Green, Bold), freshGreek, ( #> )
                       , concatWith, RawStr, render)
import           Debug.Trace (traceM)

data TypePtty = PttyPrimitive PrimitiveType
              | PttyLam [((Level, Index), BorderPtty)] TypePtty
              | PttyVar Level Index
              | PttyTop
              | PttyBot
              | PttyArrow [TypePtty] TypePtty
              | PttyTuple [TypePtty]
              | PttyRecord [(String, TypePtty)]
  deriving (Show)

type BorderPtty = U.Border TypePtty

instance Show BorderPtty where
  show (U.Border t b) = show b ++ "~" ++ show t

instance PrettyPrint BorderPtty (Int, Int) where
  pretty (U.Border PttyBot PttyTop) = txt "∅"
  pretty (U.Border t b) = pretty b <> txt "~" <> pretty t

instance PrettyPrint TypePtty (Int, Int) where
  pretty (PttyPrimitive pt) = txt $ show pt
  pretty (PttyVar lvl idx) = Italics Green #> freshGreek (lvl, idx)
  pretty PttyTop = Italics Green #> txt "⊤"
  pretty PttyBot = Italics Green #> txt "⊥"
  pretty (PttyArrow args ret) = txt "("
    <> concatWith (txt ", ") (pretty <$> args)
    <> txt ") -> "
    <> pretty ret
  pretty (PttyTuple elems) =
    txt "(" <> concatWith (txt ", ") (pretty <$> elems) <> txt ")"
  pretty (PttyRecord fields) =
    txt "{" <> concatWith (txt ", ") parseFields <> txt "}"
    where
      parseFields = (\(l, t) -> txt l <> txt ": " <> pretty t) <$> fields
  pretty (PttyLam vars body) =
    let args = parseVar . fst <$> tr vars
        hasWhere = flip any vars
          $ \(_, b) -> case b of
            U.Border PttyTop PttyBot -> False
            _ -> True
    in Bold Green #> txt "∀"
       <> concatWith (txt ", ") args
       <> Bold Green #> txt ". "
       <> pretty body
       <> if hasWhere
          then Bold Green #> txt " where "
            <> concatWith (txt "; ") parseBorders
          else txt ""
    where
      parseBorders =
        flip map vars $ \(v, b) -> parseVar v <> txt ": " <> pretty b

      parseVar (lvl, idx) = Italics Green #> freshGreek (lvl, idx)

quoteType' :: TypeValue -> TypeCheckT m TypePtty
quoteType' = \case
  TVTop -> pure PttyTop
  TVBot -> pure PttyBot
  TVPrimitive pt -> pure $ PttyPrimitive pt
  TVVar lvl idx -> pure $ PttyVar lvl idx
  TVArrow args ret -> PttyArrow <$> mapM quoteType' args <*> quoteType' ret
  TVTuple elems -> PttyTuple <$> mapM quoteType' elems
  TVRecord fields -> PttyRecord <$> mapM (secondM quoteType') fields
  TVLam vars lvl body -> PttyLam . concat <$> mapM (extractVars lvl) (tr vars)
    <*> quoteType' body
  where
    secondM f (a, b) = (a, ) <$> f b

quoteType :: Seq (Seq [Border]) -> TypeValue -> Either TypeFailure TypePtty
quoteType env = flip evalState env . runExceptT . quoteType'

normalizeBorder :: [Border] -> TypeCheckT m BorderPtty
normalizeBorder border = do
  let tops = map U.top border
      bots = map U.bot border
  -- The bottomost type of the tops
  top' <- foldM botmost TVTop tops >>= quoteType'
  -- The topmost type of the bottoms
  bot' <- foldM topmost TVBot bots >>= quoteType'
  pure $ U.Border top' bot'

extractVars
  :: Level -> TypeValue -> TypeCheckT m [((Level, Index), BorderPtty)]
extractVars lvl tv = get
  >>= \env -> case tv of
    TVVar lvl' idx
      | lvl == lvl' -> do
        let borders = env !!! lvl !!! idx
        bots <- mapM (extractVars lvl') (U.bot <$> borders)
        tops <- mapM (extractVars lvl') (U.top <$> borders)
        p <- normalizeBorder borders
        pure $ ((lvl, idx), p):concat bots ++ concat tops
    TVArrow args ret -> do
      args' <- mapM (extractVars lvl) args
      ret' <- extractVars lvl ret
      pure $ concat args' ++ ret'
    TVTuple elems -> concat <$> mapM (extractVars lvl) elems
    TVRecord fields -> concat <$> mapM (extractVars lvl . snd) fields
    _x -> pure []

testInferType :: ExprTerm -> Either TypeFailure (Pretty (Int, Int) RawStr)
testInferType expr = evalState (runExceptT m) Seq.Empty
  where
    m = do
      tv <- elaborate [] expr
      quoted <- quoteType' tv
      pure $ Green #> pretty quoted