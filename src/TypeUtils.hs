{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}

module TypeUtils where

import           Utils (Ref, type (|->), Level, Index, (!!!))
import           Syn (TypeTerm, PrimitiveType, Pattern, ExprTerm)
import           Control.Monad.State (StateT(runStateT), get, modify
                                    , MonadTrans(lift), gets, MonadState(..))
import           Control.Monad.Except (ExceptT, Except, MonadError(..))
import           Data.Map (insert, insertWith)
import           Data.Map.Lazy ((!?))
import           GHC.Arr (Array)
import           Data.Sequence (Seq((:|>)), adjust, (|>))
import           Data.Bool (bool)
import qualified Data.Sequence as Seq
import qualified Data.Foldable as Foldable

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

instance Show Border where
  show (Border t b) = ">" ++ show t ++ " " ++ show b ++ "<"

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