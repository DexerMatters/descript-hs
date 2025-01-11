{-# OPTIONS_GHC -Wno-name-shadowing #-}

{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}

module Elab where

import           Syn
import           ElabUtils
import           Utils (gets, throw, tr)
import           Control.Monad
import           Data.Bifunctor (second)
import           Data.Maybe (fromJust, isJust, fromMaybe)
import           Debug.Trace (traceM)
import           Data.Foldable (for_)

data ElabResult = ElabResult { ety :: TypeTerm, ehls :: [Int] }
  deriving (Show)

data PatternResult = PatternResult { pty :: TypeTerm
                                   , pbindings :: [(String, TypeTerm)]
                                   , phls :: [Int]
                                   }

just :: Applicative f => TypeTerm -> f ElabResult
just x = pure $ ElabResult x []

withHoles :: Applicative f => TypeTerm -> [Int] -> f ElabResult
withHoles x hs = pure $ ElabResult x hs

elaborate :: ExprTerm -> ElabState ElabResult
elaborate (Lit literal) = case literal of
  LInt _    -> just (TPrimitive PrimInt)
  LBool _   -> just (TPrimitive PrimBool)
  LUnit     -> just (TPrimitive PrimUnit)
  LString _ -> just (TPrimitive PrimString)
elaborate (Var name) = do
  bindings <- gets bindings
  case lookup name bindings of
    Just ty -> just ty
    Nothing -> throw $ UnboundVariable name
elaborate (Tuple exprs) = do
  results <- mapM elaborate exprs
  let inferred = TTuple $ map ety results
  let holes = concatMap ehls results
  withHoles inferred holes
elaborate (Record fields) = do
  results <- mapM (\(name, expr) -> (name, ) <$> elaborate expr) fields
  let inferred = TRecord $ map (second ety) results
  let holes = concatMap (ehls . snd) results
  withHoles inferred holes
elaborate Fun { args, ret_type, body } = do
  -- Infer the type of the pattern
  results <- mapM inferPattern args
  let arg_types = map pty results
  let arg_holes = concatMap phls results
  let arg_bindings = concatMap pbindings results
  -- Infer the type of the body
  ElabResult body_ty body_holes <- save'
    $ mapM_ (uncurry newBinding) arg_bindings >> elaborate body
  -- Infer the return type
  let ret_ty = case ret_type of
        Just ty -> TConv body_ty ty
        Nothing -> body_ty
  -- Construct the arrow type
  let holes = arg_holes ++ body_holes
  -- Lock all the holes
  forM_ holes $ \ref -> modifyConstr ref lock
  if null holes
    then just (TArrow arg_types ret_ty)
    else just $ tr (TLam holes $ TArrow arg_types ret_ty)
elaborate (App f args) = do
  -- Infer the types and holes of the function and arguments
  ElabResult f_type f_holes <- elaborate f
  arg_results <- mapM elaborate args
  let input_types = map ety arg_results
  let holes = f_holes ++ concatMap ehls arg_results
  let reduce f_type = case f_type of
        -- If it is applied with wrong arity, throw an error
        TArrow arg_types _
          | length arg_types /= length input_types -> throw
            $ MismatchedArity (length arg_types) (length input_types)
        -- If it is a lambda, reduce it
        TArrow arg_types ret_type -> do
          zipWithM_ unify input_types arg_types
          let cvrts = zipWith TConv input_types arg_types
          -- pure (TSeq (cvrts ++ [ret_type]), arg_types, [])
          pure (TSeq $ cvrts ++ [ret_type], arg_types, [])
        -- If it is a type lambda, preserve the holes
        TLam holes' f_type' -> do
          (ret_type, arg_types, holes'') <- reduce f_type'
          pure (TApp (TLam holes' ret_type) arg_types input_types, [], holes'')
        -- If it is an applied type lambda, reduce it
        TApp (TLam holes'' ret_type) args' inputs' -> do
          (ret_type', _, holes') <- reduce ret_type
          pure (TApp (TLam holes'' ret_type') args' inputs', [], holes')
        TSeq seq -> do
          (ret_type, _, holes') <- reduce (last seq)
          pure (TSeq $ init seq ++ [ret_type], [], holes')
        -- If it is a type variable
        TVar ref -> do
          free <- isFree ref
          -- If it is free, unify it with a new arrow type
          if free
            then do
              ref' <- newTypeVar
              let func = TArrow input_types (TVar ref')
              unify f_type func
              pure (TVar ref', input_types, [ref'])
            else 
              -- If it is not free, reduce it according to its constraints
              do
                constr <- fromJust <$> getConstr ref
                (top_ret, top_args, top_hls) <- unzip3
                  <$> mapM reduce (tops constr)
                (bot_ret, bot_args, bot_hls) <- unzip3
                  <$> mapM reduce (bots constr)
                let arg_types = concat top_args ++ concat bot_args
                let holes = concat top_hls ++ concat bot_hls
                let newConstr = Constr top_ret bot_ret False
                ref' <- newTypeVar
                modifyConstr ref $ const newConstr
                pure (TVar ref', arg_types, ref':holes)
        _ -> throw $ CannotBeApplied f_type
  (inferred, _, holes') <- reduce f_type
  withHoles inferred (holes' ++ holes)
elaborate (Proj expr label) = do
  ElabResult expr_ty expr_holes <- elaborate expr
  let reduce rcd_type = case rcd_type of
        TRecord flds -> case lookup label flds of
          Just ty -> pure (ty, [])
          Nothing -> throw $ UndefinedLabel label
        TLam holes rcd_type' -> do
          (ty, holes') <- reduce rcd_type'
          pure (TLam holes ty, holes')
        TApp rcd_type' _ inputs -> do
          rcd_type'' <- simpleEval [] rcd_type'
          case rcd_type'' of
            TLam refs body -> simpleEval (zip refs inputs) body >>= reduce
            _ -> throw $ CannotBeProjected rcd_type label
        TVar ref -> do
          free <- isFree ref
          if free
            then do
              ref' <- newTypeVar
              let rcd = TRecord [(label, TVar ref')]
              unify rcd_type rcd
              pure (TVar ref', [ref'])
            else do
              constr <- fromJust <$> getConstr ref
              tops' <- mapM reduce (tops constr)
              bots' <- mapM reduce (bots constr)
              let holes = concatMap snd tops' ++ concatMap snd bots'
              let newConstr = Constr (map fst tops') (map fst bots') False
              ref' <- newTypeVar
              modifyConstr ref $ const newConstr
              pure (TVar ref', ref':holes)
        _ -> throw $ CannotBeProjected rcd_type label
  (inferred, holes) <- reduce expr_ty
  withHoles inferred (expr_holes ++ holes)
elaborate (Let { pat, rhs, body }) = do
  -- Check the type of the right-hand side
  ElabResult rhs_ty rhs_holes <- elaborate rhs
  PatternResult _ pbindings _ <- checkPattern pat rhs_ty
  -- Infer the type of the body
  ElabResult body_ty body_holes <- save'
    $ do
      mapM_ (uncurry newBinding) pbindings
      elaborate body
  withHoles body_ty (rhs_holes ++ body_holes)
elaborate (TypeAlias { name, poly, ty, body }) = case poly of
  Nothing   -> do
    ref <- newTypeVar
    indexed_ty <- indexType (Just (name, ref)) [] ty
    ElabResult body_ty body_holes
      <- save'' $ newTypeBinding name indexed_ty >> elaborate body
    indexed_body <- indexType Nothing [(name, ref)] body_ty
    modifyConstr ref lock
    withHoles (TLet ref indexed_ty indexed_body) body_holes
  Just vars -> do
    refs <- mapM (const newTypeVar) vars
    ref <- newTypeVar
    indexed_ty <- TLam refs <$> indexType (Just (name, ref)) (zip vars refs) ty
    ElabResult body_ty body_holes
      <- save'' $ newTypeBinding name indexed_ty >> elaborate body
    -- lock the holes
    forM_ (ref:refs) $ \ref -> modifyConstr ref lock
    -- index the type
    indexed_body <- indexType Nothing [(name, ref)] body_ty
    withHoles (TLet ref indexed_ty indexed_body) body_holes
elaborate (If { cond, then_branch, else_branch }) = do
  ElabResult cond_ty cond_holes <- elaborate cond
  ElabResult then_ty then_holes <- elaborate then_branch
  ElabResult else_ty else_holes <- elaborate else_branch
  unify cond_ty (TPrimitive PrimBool)
  unify then_ty else_ty
  pure
    $ ElabResult
      (TSeq [TConv then_ty else_ty, TConv else_ty then_ty])
      (cond_holes ++ then_holes ++ else_holes)
elaborate (Seq exprs) = do
  results <- mapM elaborate exprs
  let inferred = TSeq $ map ety results
  let holes = concatMap ehls results
  withHoles inferred holes
elaborate (Keyword "check" (Right ty)) = pure $ ElabResult ty []
elaborate (Keyword _ _) = error "Impossible"

inferPattern :: Pattern -> ElabState PatternResult
inferPattern (PAtom x) = do
  ref <- newTypeVar
  let inferred = TVar ref
  let bindings = [(x, inferred)]
  pure $ PatternResult inferred bindings [ref]
inferPattern (PTuple pats) = do
  results <- mapM inferPattern pats
  let inferred = TTuple $ map pty results
  let bindings = concatMap pbindings results
  let holes = concatMap phls results
  pure $ PatternResult inferred bindings holes
inferPattern (PRecord fields) = do
  results <- mapM (\(name, pat) -> (name, ) <$> inferPattern pat) fields
  let inferred = TRecord $ map (second pty) results
  let bindings = concatMap (pbindings . snd) results
  let holes = concatMap (phls . snd) results
  pure $ PatternResult inferred bindings holes
inferPattern PWildcard = do
  ref <- newTypeVar
  let inferred = TVar ref
  pure $ PatternResult inferred [] [ref]
inferPattern (PAnnot pat ty) = do
  checkPattern pat ty

checkPattern :: Pattern -> TypeTerm -> ElabState PatternResult
checkPattern t (TFree x) = lookupType x >>= checkPattern t
checkPattern t (TApp lam _ inputs) = simpleEval [] lam
  >>= \case
    TLam refs ty -> simpleEval (zip refs inputs) ty
    _ -> throw $ CannotBeApplied lam
  >>= checkPattern t
checkPattern (PAtom x) ty = do
  (ty', holes) <- indexHoles ty
  pure $ PatternResult ty' [(x, ty')] holes
checkPattern (PTuple pats) (TTuple tys) = do
  results <- zipWithM checkPattern pats tys
  let inferred = TTuple $ map pty results
  let bindings = concatMap pbindings results
  let holes = concatMap phls results
  pure $ PatternResult inferred bindings holes
checkPattern a@(PRecord fields) b@(TRecord tys) = do
  results <- forM fields
    $ \(name, pat) -> do
      case lookup name tys of
        Just ty -> checkPattern pat ty
        Nothing -> throw $ BadPattern b a
  let inferred = map pty results
  let bindings = concatMap pbindings results
  let holes = concatMap phls results
  let names = map fst fields
  if length names /= length tys
    then throw $ BadPattern b a
    else pure $ PatternResult (TRecord $ zip names inferred) bindings holes
checkPattern PWildcard ty = do
  (ty', holes) <- indexHoles ty
  pure $ PatternResult ty' [] holes
checkPattern (PAnnot _ _) _ = throw DuplicatedAnnotation
checkPattern a b = throw $ BadPattern b a

unify :: TypeTerm -> TypeTerm -> ElabState ()
unify (TVar ref) ty = isFree ref
  >>= \case
    True -> modifyConstr ref (pushBot ty)
    _    -> pure ()
unify ty (TVar ref) = isFree ref
  >>= \case
    True -> modifyConstr ref (pushTop ty)
    _    -> pure ()
unify (TTuple tys1) (TTuple tys2) = zipWithM_ unify tys1 tys2
unify (TRecord tys1) (TRecord tys2) = do
  forM_ tys1 $ \(name, ty1) -> for_ (lookup name tys2) (unify ty1)
unify (TArrow args1 ret1) (TArrow args2 ret2) = do
  zipWithM_ unify args1 args2
  unify ret1 ret2
unify _ _ = pure ()

indexType
  :: Maybe (String, Int) -> [(String, Int)] -> TypeTerm -> ElabState TypeTerm
indexType self bds = \case
  TFree s
    | Just s == fmap fst self -> pure $ TFix $ snd (fromJust self)
  TFree s -> case lookup s (tr bds) of
    Just i  -> pure $ TVar i
    Nothing -> pure $ TFree s
  TTuple tys -> TTuple <$> mapM (indexType self bds) tys
  TRecord tys -> TRecord
    <$> mapM (\(name, ty) -> (name, ) <$> indexType self bds ty) tys
  TArrow args ret -> TArrow <$> mapM (indexType self bds) args
    <*> indexType self bds ret
  TLam holes ty -> TLam holes <$> indexType self bds ty
  TApp ty args inputs -> TApp <$> indexType self bds ty
    <*> pure args
    <*> mapM (indexType self bds) inputs
  TSeq tys -> TSeq <$> mapM (indexType self bds) tys
  TLet name ty body
    -> TLet name <$> indexType self bds ty <*> indexType self bds body
  ty -> pure ty

indexHoles :: TypeTerm -> ElabState (TypeTerm, [Int])
indexHoles = \case
  THole -> do
    ref <- newTypeVar
    pure (TVar ref, [ref])
  TTuple tys -> do
    (tys', holes) <- mapAndUnzipM indexHoles tys
    pure (TTuple tys', concat holes)
  TRecord tys -> do
    (names, results)
      <- mapAndUnzipM (\(name, ty) -> (name, ) <$> indexHoles ty) tys
    let tys' = zip names (map fst results)
    let holes = concatMap snd results
    pure (TRecord tys', holes)
  TArrow args ret -> do
    (args', args_holes) <- mapAndUnzipM indexHoles args
    (ret', ret_holes) <- indexHoles ret
    pure (TArrow args' ret', concat args_holes ++ ret_holes)
  TLam holes ty -> do
    (ty', ty_holes) <- indexHoles ty
    pure (TLam holes ty', ty_holes)
  TApp ty args inputs -> do
    (ty', ty_holes) <- indexHoles ty
    (args', args_holes) <- mapAndUnzipM indexHoles args
    (inputs', inputs_holes) <- mapAndUnzipM indexHoles inputs
    pure
      ( TApp ty' args' inputs'
      , ty_holes ++ concat args_holes ++ concat inputs_holes)
  TSeq tys -> do
    (tys', holes) <- mapAndUnzipM indexHoles tys
    pure (TSeq tys', concat holes)
  TLet name ty body -> do
    (ty', ty_holes) <- indexHoles ty
    (body', body_holes) <- indexHoles body
    pure (TLet name ty' body', ty_holes ++ body_holes)
  ty -> pure (ty, [])