{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}

{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module TypeUtils where

import           Utils (type (|->), Level, Index, (!!!), hashIntPair, tr
                      , zipWith')
import           Syn (PrimitiveType, Pattern, TypeDescriptor)
import           Control.Monad.Except (ExceptT)
import           Data.Sequence (Seq((:|>)), adjust, (|>))
import qualified Data.Sequence as Seq
import qualified Data.Foldable as Foldable
import           Pretty (PrettyPrint(..), txt, concatWith, space, freshGreek
                       , Pretty(Empty), RawStr, Color(..), ( #> ), render)
import           Control.Monad.State (StateT, modify, gets, MonadState(..))
import qualified Utils as U

-- | Evaluated Types



data TypeValue = TVPrimitive PrimitiveType
               | TVLam [TypeValue] Level TypeValue
               | TVVar TypeDescriptor Level Index
               | TVTop    -- Most general type
               | TVBot    -- Most specific type
               | TVArrow [TypeValue] TypeValue
               | TVTuple [TypeValue]
               | TVRecord [(String, TypeValue)]
  deriving Show

type Border = U.Border TypeValue

instance Show Border where
  show (U.Border t b) = ">" ++ show t ++ " " ++ show b ++ "<"

extractVars :: Seq (Seq [Border]) -> TypeValue -> [(TypeValue, [Border])]
extractVars env = \case
  TVVar td lvl idx
    | lvl == Seq.length env - 1
      -> let border = env !!! lvl !!! idx
             tops = concatMap (extractVars env . U.top) border
             bots = concatMap (extractVars env . U.bot) border
         in (TVVar td lvl idx, border):tops ++ bots
  TVArrow args ret -> concatMap (extractVars env) args ++ extractVars env ret
  TVTuple elems -> concatMap (extractVars env) elems
  TVRecord fields -> concatMap (extractVars env . snd) fields
  _ -> []

-- | Environment for type checking

data TypeEnv = TypeEnv { bindings :: String |-> TypeValue
                       , level :: Level
                       , typeBindings :: Seq (Seq TypeValue)
                       , constraints :: Constraints
                       }

data TypeFailure =
    UndefinedType TypeValue
  | UnboundVariable String
  | TypeMismatch TypeValue TypeValue
  | BadPattern Pattern TypeValue
  | BadConversion TypeValue TypeValue
  | MissingField String
  | TypeVariableOutOfScope Level Index
  | NotApplicable TypeValue
  | NotProjectable TypeValue
  deriving Show

type TypeResult a = Either TypeFailure a

type Constraints = Seq (Seq [Border])

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
  modify (adjust (|> [U.Border TVTop TVBot]) lvl)
  pure idx

save :: TypeCheckT m a -> TypeCheckT m a
save m = do
  s <- get
  a <- m
  put s
  pure a
