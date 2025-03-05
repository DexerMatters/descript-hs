{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module TypeUtils where

import Control.Monad.Except (ExceptT, MonadError (catchError, throwError), runExceptT)
import Control.Monad.Identity (Identity)
import Control.Monad.State (StateT (runStateT), gets, modify)
import Control.Monad.State.Lazy (evalStateT)
import Data.Sequence (Seq ((:|>)), adjust, (|>))
import qualified Data.Sequence as Seq
import Syn
  ( ExprTerm',
    Pattern',
    PrimitiveType,
    TypeDescriptor,
    TypeTerm',
  )
import Utils (FI (FI), Index, Level, Range (Range), WithFI, (!!!), type (|->))
import qualified Utils as U

-- | Evaluated Types
data TypeValue
  = TVPrimitive PrimitiveType
  | TVLam [TypeValue'] Level TypeValue'
  | TVVar TypeDescriptor Level Index
  | TVTop -- Most general type
  | TVBot -- Most specific type
  | TVArrow [TypeValue'] TypeValue'
  | TVTuple [TypeValue']
  | TVRecord [(String, TypeValue')]
  deriving (Show)

type TypeValue' = U.WithFI TypeValue

type Border = U.Border TypeValue

type DiagnosticFunctions m =
  (Monad m) =>
  ( TypeTerm' ->
    TypeCheckT m TypeValue' ->
    TypeCheckT m TypeValue',
    ExprTerm' ->
    TypeCheckT m TypeValue' ->
    TypeCheckT m TypeValue'
  )

instance Show Border where
  show (U.Border t b) = ">" ++ show t ++ " " ++ show b ++ "<"

-- | Environment for type checking
data TypeFailure
  = UndefinedType TypeValue'
  | UnboundVariable String
  | TypeMismatch TypeValue' TypeValue'
  | BadPattern Pattern' TypeValue'
  | BadConversion TypeValue' TypeValue'
  | MissingField String
  | TooManyFields
  | TypeVariableOutOfScope Level Index
  | NotApplicable TypeValue'
  | NotProjectable TypeValue'
  deriving (Show)

type Constraints = Seq (Seq [Border])

-- | Monad for type checking
data TypeEnv = TypeEnv
  { getConstrs :: Seq (Seq [Border]),
    traces :: [Either (WithFI TypeFailure) TypeValue'],
    scopes :: [(Range, String |-> TypeValue')]
  }

type TypeCheckT m a =
  (Monad m) =>
  ExceptT (U.WithFI TypeFailure) (StateT TypeEnv m) a

-- | Auxiliary functions
gets' :: (Seq (Seq [Border]) -> a) -> TypeCheckT m a
gets' f = gets (f . getConstrs)

get' :: TypeCheckT m (Seq (Seq [Border]))
get' = gets getConstrs

modify' :: (Seq (Seq [Border]) -> Seq (Seq [Border])) -> TypeCheckT m ()
modify' f = modify $ \s -> s {getConstrs = f $ getConstrs s}

uplevel :: TypeCheckT m Level
uplevel = do
  lvl <- gets' Seq.length
  modify' (|> Seq.empty)
  pure lvl

downlevel :: TypeCheckT m ()
downlevel = modify' $
  \case
    (xs :|> _) -> xs
    _ -> error "No levels to pop"

getCurrentLevel :: TypeCheckT m Level
getCurrentLevel = gets' (subtract 1 . Seq.length)

putBorder :: Level -> Index -> Border -> TypeCheckT m ()
putBorder lvl idx border = modify' $ flip adjust lvl $ adjust (border :) idx

setBorder :: Level -> Index -> [Border] -> TypeCheckT m ()
setBorder lvl idx borders =
  modify' $ flip adjust lvl $ adjust (const borders) idx

getBorder :: Level -> Index -> TypeCheckT m [Border]
getBorder lvl idx = gets' $ (!!! idx) . (!!! lvl)

putTrace :: Either (WithFI TypeFailure) TypeValue' -> TypeCheckT m ()
putTrace trace = modify $ \s -> s {traces = trace : traces s}

newVar :: Level -> TypeCheckT m Index
newVar lvl = do
  idx <- gets' (Seq.length . (!!! lvl))
  modify' (adjust (|> [U.Border TVTop TVBot]) lvl)
  pure idx

runTypeChecker ::
  (Monad m) => TypeCheckT m a -> m (Either (U.WithFI TypeFailure) a, TypeEnv)
runTypeChecker = flip runStateT (TypeEnv Seq.empty [] []) . runExceptT

runTypeChecker' ::
  (Monad m) => TypeEnv -> TypeCheckT m a -> m (Either (U.WithFI TypeFailure) a)
runTypeChecker' env = flip evalStateT env . runExceptT

execTypeChecker ::
  (Monad m) => TypeCheckT m a -> m TypeEnv
execTypeChecker = fmap snd . runTypeChecker

saveScope :: FI -> String |-> TypeValue' -> TypeCheckT m ()
saveScope (FI _ s e) scope = modify $ \s' -> s' {scopes = (Range s e, scope) : scopes s'}

diagnose :: (a -> TypeValue') -> TypeCheckT m a -> TypeCheckT m a
diagnose f action = catchError
  ( do
      result <- action
      putTrace (Right $ f result)
      pure result
  )
  $ \err -> do
    putTrace (Left err)
    throwError err