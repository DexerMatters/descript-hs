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
import Data.Bifunctor (second)
import Data.List (nub)

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
  TLam rigid refs ty -> TLam rigid refs <$> simpleEval bds ty
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




indexType :: Maybe (String, Int) -> [(String, Int)] -> TypeTerm -> TypeTerm
indexType self bds = \case
  TFree s
    | Just s == fmap fst self -> TFix $ snd (fromJust self)
  TFree s -> case lookup s bds of
    Just i  -> TVar i
    Nothing -> TFree s
  TTuple tys -> TTuple $ map (indexType self bds) tys
  TRecord tys -> TRecord $ map (second (indexType self bds)) tys
  TArrow args ret
    -> TArrow (map (indexType self bds) args) (indexType self bds ret)
  TLam rigid holes ty -> TLam rigid holes $ indexType self bds ty
  TApp ty args inputs -> TApp (indexType self bds ty) args
    $ map (indexType self bds) inputs
  TSeq tys -> TSeq $ map (indexType self bds) tys
  TLet name ty body
    -> TLet name (indexType self bds ty) (indexType self bds body)
  ty -> ty

indexType' :: Maybe (String, Int) -> [(String, Int)] -> TypeTerm -> (TypeTerm, [Int])
indexType' self bds = \case
  TFree s
    | Just s == fmap fst self -> (TFix $ snd (fromJust self), [])
  TFree s -> case lookup s bds of
    Just i  -> (TVar i, [i])
    Nothing -> (TFree s, [])
  TTuple tys -> let (tys', refs) = unzip $ fmap (indexType' self bds) tys in 
    (TTuple tys', concat refs)

  TRecord tys -> 
    let (labels', fields) = unzip $ fmap (second (indexType' self bds)) tys in 
    let (tys', refs) = unzip fields in
    (TRecord $ zip labels' tys', concat refs)
  TArrow args ret
    -> 
    let (args', refs) = unzip $ fmap (indexType' self bds) args in
    let (ret', refs') = indexType' self bds ret in
    (TArrow args' ret', concat refs ++ refs')
  TLam rigid holes ty -> 
    let (ty', refs) = indexType' self bds ty in
    (TLam rigid holes ty', refs)
  TApp ty args inputs -> 
    let (ty', refs) = indexType' self bds ty in
    let (args', refs') = unzip $ fmap (indexType' self bds) args in
    let (inputs', refs'') = unzip $ fmap (indexType' self bds) inputs in
    (TApp ty' args' inputs',  refs ++ concat refs' ++ concat refs'')
  TSeq tys -> 
    let (tys', refs) = unzip $ fmap (indexType' self bds) tys in
    (TSeq tys, concat refs)
  TLet name ty body -> 
    let (ty', refs) = indexType' self bds ty in
    let (body', refs') = indexType' self bds body in
    (TLet name ty' body', refs ++ refs')
  ty -> (ty, [])