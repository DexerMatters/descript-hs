{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}

module EvalTUtils where

import           Syn
import           Utils
import qualified ElabUtils as Elab
import           GHC.Arr ((!), Array, array, (//), assocs)
import           Data.Maybe (isJust)
import           ElabUtils (Constr(..), ConstrEnv)

data EvalTError = InadequateTypeArity TypeVal TypeVal
                | UnboundTypeVariable Int
                | UnboundTypeIdent String
                | UnexpectedUndone
                | AmbiguousTypeVariable Int
                | BadConversion TypeVal TypeVal
                | UnexpectedHole
  deriving (Show)

data TypeVal = TVVar Int
             | TVFix TLazy
             | TVPrimitive PrimitiveType
             | TVArrow [TypeVal] TypeVal
             | TVTuple [TypeVal]
             | TVRecord [(String, TypeVal)]
             | TVLam TClosure
  deriving (Show)

data TypePretty = PttyVar String
                | PttyPrimitive PrimitiveType
                | PttyArrow [TypePretty] TypePretty
                | PttyTuple [TypePretty]
                | PttyRecord [(String, TypePretty)]
                | PttyLam [String] TypePretty
  deriving (Show)

type BindingEnv = Array Int (Maybe TypeVal)

data EvalTEnv =
  EvalTEnv { constrs :: ConstrEnv
           , bindings :: BindingEnv
           , freeBindings :: [(String, EvalTStage)]
           , fresh :: Int
           , pttyBindings :: [(Int, String)]
           , ident :: Int
           , fixFlag :: Bool
           }

type EvalTState = MState EvalTEnv EvalTError

data EvalTStage = Evaluated TypeVal
                | Unevaluated TypeTerm
                | EvaluationError EvalTError

instance Show EvalTStage where
  show :: EvalTStage -> String
  show (Evaluated ty) = show ty
  show (Unevaluated ty) = show ty
  show (EvaluationError err) = show err

data TClosure = TClosure [Int] EvalTEnv TypeTerm

data TLazy = TLazy EvalTEnv TypeTerm
  deriving (Show)

instance Show EvalTEnv where
  show :: EvalTEnv -> String
  show EvalTEnv { bindings } = "BINGINGS: " ++ bindingsStr
    where
      bindingsStr =
        let as = filter (isJust . snd) (assocs bindings)
        in concatMap
             (("\t\n" ++) . (\(i, ty) -> show i ++ " : " ++ show ty))
             as

instance Show TClosure where
  show :: TClosure -> String
  show (TClosure refs _ ty) = "<" ++ show refs ++ " " ++ show ty ++ ">"

fromElabEnv :: Elab.ElabEnv -> EvalTEnv
fromElabEnv Elab.ElabEnv { Elab.constrs = c } =
  EvalTEnv { constrs = c
           , bindings = array (0, 1024) [(i, Nothing) | i <- [0 .. 1024]]
           , freeBindings = []
           , fresh = 0
           , pttyBindings = []
           , ident = 0
           , fixFlag = False
           }

newBinding :: Int -> TypeVal -> EvalTState ()
newBinding n ty = modify
  $ \env -> env { bindings = bindings env // [(n, Just ty)] }

lookupBinding :: Int -> EvalTState TypeVal
lookupBinding ref = gets bindings
  >>= (\case
         Just ty -> pure ty
         Nothing -> throw $ UnboundTypeVariable ref)
  . (! ref)

lookupBinding' :: Int -> EvalTState TypeVal
lookupBinding' ref = gets bindings
  >>= (\case
         Just ty -> pure ty
         Nothing -> pure $ TVVar ref)
  . (! ref)

lookupBinding'' :: Int -> EvalTState TypeVal
lookupBinding'' ref = gets bindings
  >>= (\case
         Just ty -> pure ty
         Nothing -> pure undefined)
  . (! ref)

existBinding :: Int -> EvalTState Bool
existBinding ref = (\case
                      Just (TVVar _) -> False
                      Just _         -> True
                      Nothing        -> False)
  . (! ref)
  <$> gets bindings

getTops :: Int -> EvalTState [TypeTerm]
getTops n = do
  EvalTEnv { constrs } <- get
  case constrs ! n of
    Just (Constr tops _ _) -> pure tops
    Nothing -> throw $ UnboundTypeVariable n

getBots :: Int -> EvalTState [TypeTerm]
getBots n = do
  EvalTEnv { constrs } <- get
  case constrs ! n of
    Just (Constr _ bots _) -> pure bots
    Nothing -> throw $ UnboundTypeVariable n

lookupFresh :: Int -> EvalTState String
lookupFresh n =
  let idents = map (:[]) ['T' .. 'Z']
  in do
       bs <- gets pttyBindings
       case lookup n bs of
         Just s  -> pure s
         Nothing -> do
           let s = if n < length idents
                   then idents !! n
                   else "T" ++ show n
           modify $ \env -> env { pttyBindings = (n, s):bs }
           pure s

block :: EvalTState String -> EvalTState String
block f = do
  modify $ \env -> env { ident = ident env + 1 }
  s <- f
  modify $ \env -> env { ident = ident env - 1 }
  pure s

makeIndent :: EvalTState String
makeIndent = do
  n <- gets ident
  pure $ replicate n '\t'


