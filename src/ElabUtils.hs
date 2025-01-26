{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module ElabUtils where


import           Syn
import           Utils (MState (runMState), modify, gets, throw)
import GHC.Arr ((//), (!), assocs, Array, array)
import Data.Maybe (fromJust, isJust)

data ElabError = NeverHappens
               | UnboundVariable String
               | UnboundTypeVariable String
               | DuplicatedAnnotation
               | BadPattern TypeTerm Pattern
               | MismatchedArity Int Int
               | CannotBeApplied TypeTerm
               | UndefinedLabel String
               | CannotBeProjected TypeTerm String
               
  deriving (Show)

data ElabEnv = ElabEnv { counter :: Int
                       , bindings :: [(String, ElabStage)]
                       , typeBindings :: [(String, TypeTerm)]
                       , constrs :: ConstrEnv
                       }

data ElabStage = Elaborated TypeTerm | Unelaborated ExprTerm | ElaborationError ElabError

instance Show ElabStage where
  show (Elaborated ty) = show ty
  show (Unelaborated expr) = show expr
  show (ElaborationError err) = show err

type ElabState = Utils.MState ElabEnv ElabError

instance Show ElabEnv where
  show ElabEnv { bindings, constrs } =
    "BINGINGS: \t" ++ bindingStr ++ "\n" ++
    "CONSTRS: \t" ++ constrStr ++ "\n"
    where bindingStr = concatMap (("\t\n" ++) . (\(name, ty) -> name ++ " : " ++ show ty)) bindings
          constrStr = let as = filter (isJust . snd) (assocs constrs)
                      in concatMap (("\t\n" ++) . (\(i, ty) -> show i ++ " : " ++ show ty)) as

emptyEnv :: ElabEnv
emptyEnv = ElabEnv 0 [] [] initialConstrEnv


fresh :: ElabState Int
fresh = do
  c <- Utils.gets counter
  Utils.modify $ \env -> env { counter = c + 1 }
  pure c

newTypeVar :: ElabState Int
newTypeVar = do
  ref <- fresh
  Utils.modify $ \env -> env {
    constrs = env.constrs // [(ref, Just $ Constr [] [] False)]
  }
  pure ref

newBinding :: String -> TypeTerm -> ElabState ()
newBinding name ty = do
  Utils.modify $ \env -> env {
    bindings = (name, Elaborated ty):bindings env
  }

newTypeBinding :: String -> TypeTerm -> ElabState ()
newTypeBinding name ty = do
  Utils.modify $ \env -> env {
    typeBindings = (name, ty):typeBindings env
  }

lookupType :: String -> ElabState TypeTerm
lookupType name = do
  env <- Utils.gets typeBindings
  case lookup name env of
    Just ty -> pure ty
    Nothing -> Utils.throw $ UnboundVariable name

getConstr :: Int -> ElabState (Maybe Constr)
getConstr ref = do
  env <- Utils.gets constrs
  pure $ env ! ref

modifyConstr :: Int -> (Constr -> Constr) -> ElabState ()
modifyConstr ref f = do
  Utils.modify $ \env -> env {
    constrs = env.constrs // [(ref, Just . f $ fromJust $ env.constrs ! ref)]
  }

isFree :: Int -> ElabState Bool
isFree ref = do
  Constr { locked } <- fromJust <$> getConstr ref
  pure (not locked)


save' :: ElabState a -> ElabState a
save' f = do
  s <- Utils.gets bindings
  a <- f
  Utils.modify $ \env -> env { bindings = s }
  pure a

save'' :: ElabState a -> ElabState a
save'' f = do
  s <- Utils.gets typeBindings
  a <- f
  Utils.modify $ \env -> env { typeBindings = s }
  pure a


simpleEval :: [(Int, TypeTerm)] -> TypeTerm -> ElabState TypeTerm
simpleEval bds = \case
  TVar n -> case lookup n bds of
    Just ty -> pure ty
    Nothing -> pure $ TVar n
  TFree s -> lookupType s
  TPrimitive p -> pure $ TPrimitive p
  TArrow args ret -> TArrow <$> mapM (simpleEval bds) args
    <*> simpleEval bds ret
  TTuple ts -> TTuple <$> mapM (simpleEval bds) ts
  TRecord fields -> TRecord
    <$> mapM (\(name, ty) -> (name, ) <$> simpleEval bds ty) fields
  TLam refs ty -> TLam refs <$> simpleEval bds ty
  TApp lam args inputs -> TApp <$> simpleEval bds lam
    <*> mapM (simpleEval bds) args
    <*> pure inputs
  TConv from to -> TConv <$> simpleEval bds from <*> simpleEval bds to
  TSeq seq -> simpleEval bds (last seq)
  TLet ref ty body -> TLet ref <$> simpleEval bds ty
    <*> simpleEval ((ref, ty):bds) body
  TFix n -> pure $ TVar n
  THole -> pure THole


data Constr = Constr { tops :: [TypeTerm], bots :: [TypeTerm], locked :: Bool }
  deriving (Show)

pushTop :: TypeTerm -> Constr -> Constr
pushTop t c = c { tops = t:tops c }

pushBot :: TypeTerm -> Constr -> Constr
pushBot t c = c { bots = t:bots c }

newConstr :: Constr
newConstr = Constr [] [] False

newConstr' :: Constr
newConstr' = Constr [] [] True

lock :: Constr -> Constr
lock c = c { locked = True }

type ConstrEnv = Array Int (Maybe Constr)

initialConstrEnv :: ConstrEnv
initialConstrEnv = array (0, 1024) [(i, Nothing) | i <- [0 .. 1024]]