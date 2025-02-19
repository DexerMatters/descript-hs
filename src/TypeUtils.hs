{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}

{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module TypeUtils where

import           Utils (type (|->), Level, Index, (!!!), hashIntPair, tr)
import           Syn (PrimitiveType, Pattern)
import           Control.Monad.Except (ExceptT)
import           Data.Sequence (Seq((:|>)), adjust, (|>))
import qualified Data.Sequence as Seq
import qualified Data.Foldable as Foldable
import           Pretty (PrettyPrint(..), txt, concatWith, space, freshGreek
                       , Pretty(Empty), RawStr)
import           Control.Monad.State (StateT, modify, gets, MonadState(..))

-- | Evaluated Types

data TypeValue = TVPrimitive PrimitiveType
               | TVLam [TypeValue] TClosure
               | TVVar Level Index
               | TVTop    -- Most general type
               | TVBot    -- Most specific type
               | TVArrow [TypeValue] TypeValue
               | TVTuple [TypeValue]
               | TVRecord [(String, TypeValue)]
  deriving Show

data Border = Border { top :: TypeValue, bot :: TypeValue }

data TClosure = TClosure TypeValue (Seq (Seq [Border]))

instance Show TClosure where
  show (TClosure tv env) =
    show tv ++ " " ++ show (fmap Foldable.toList (Foldable.toList env))

instance PrettyPrint TClosure where
  pretty (TClosure tv _) = pretty tv

instance Show Border where
  show (Border t b) = ">" ++ show t ++ " " ++ show b ++ "<"

instance PrettyPrint Border where
  pretty (Border t b) = pretty b <> txt "~" <> pretty t

instance PrettyPrint TypeValue where
  pretty :: TypeValue -> Pretty Int RawStr
  pretty (TVPrimitive pt) = txt $ show pt
  pretty (TVLam args (TClosure tv env)) =
    let vars = tr (concatMap (extractVars env) args)
        args' = fst <$> vars
        hasWhere = not $ all (null . snd) vars
    in txt "∀"
       <> concatWith space (pretty <$> args')
       <> txt ". "
       <> pretty tv
       <> if hasWhere
          then txt " where " <> concatWith (txt "; ") (parseVar <$> vars)
          else Empty
    where
      parseVar (_, []) = Empty
      parseVar (tv', bs) =
        pretty tv' <> txt ": " <> concatWith (txt ", ") (pretty <$> bs)
  pretty (TVVar lvl idx) = freshGreek (hashIntPair (lvl, idx))
  pretty TVTop = txt "⊤"
  pretty TVBot = txt "⊥"
  pretty (TVArrow args ret) = txt "("
    <> concatWith (txt ", ") (pretty <$> args)
    <> txt ") -> "
    <> pretty ret
  pretty (TVTuple elems) =
    txt "(" <> concatWith (txt ", ") (pretty <$> elems) <> txt ")"
  pretty
    (TVRecord fields) = txt "{" <> concatWith (txt ", ") parseFields <> txt "}"
    where
      parseFields = (\(l, t) -> txt l <> txt ": " <> pretty t) <$> fields

extractVars :: Seq (Seq [Border]) -> TypeValue -> [(TypeValue, [Border])]
extractVars env = \case
  TVVar lvl idx
    | lvl == Seq.length env - 1
      -> let border = env !!! lvl !!! idx
             tops = concatMap (extractVars env . top) border
             bots = concatMap (extractVars env . bot) border
         in (TVVar lvl idx, border):tops ++ bots
  TVArrow args ret -> concatMap (extractVars env) args ++ extractVars env ret
  TVTuple elems -> concatMap (extractVars env) elems
  TVRecord fields -> concatMap (extractVars env . snd) fields
  _ -> []

-- | Environment for type checking

data TypeEnv = TypeEnv { bindings :: String |-> TypeValue
                       , level :: Level
                       , typeBindings :: Seq (Seq TypeValue)
                       , constraints :: Seq (Seq [Border])
                       }

data TypeFailure = UndefinedType TypeValue
                 | UnboundVariable String
                 | TypeMismatch TypeValue TypeValue
                 | BadPattern Pattern TypeValue
                 | BadConversion TypeValue TypeValue
                 | MissingField String
  deriving Show

type TypeResult a = Either TypeFailure a

-- | Monad for type checking

type TypeCheckT m a = Monad m
  => ExceptT TypeFailure (StateT (Seq (Seq [Border])) m) a

-- | Auxiliary functions

uplevel :: TypeCheckT m Level
uplevel = do
  lvl <- gets Seq.length
  modify (|> Seq.empty)
  pure lvl

downlevel :: TypeCheckT m ()
downlevel = modify
  $ \case
    (xs :|> _) -> xs
    _          -> error "No levels to pop"

getCurrentLevel :: TypeCheckT m Level
getCurrentLevel = gets (subtract 1 . Seq.length)

putBorder :: Level -> Index -> Border -> TypeCheckT m ()
putBorder lvl idx border = modify $ flip adjust lvl $ adjust (border:) idx

setBorder :: Level -> Index -> [Border] -> TypeCheckT m ()
setBorder lvl idx borders =
  modify $ flip adjust lvl $ adjust (const borders) idx

getBorder :: Level -> Index -> TypeCheckT m [Border]
getBorder lvl idx = gets $ (!!! idx) . (!!! lvl)

newVar :: Level -> TypeCheckT m Index
newVar lvl = do
  idx <- gets (Seq.length . (!!! lvl))
  modify (adjust (|> []) lvl)
  pure idx

save :: TypeCheckT m a -> TypeCheckT m a
save m = do
  s <- get
  a <- m
  put s
  pure a