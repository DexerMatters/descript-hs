{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BlockArguments #-}

{-# OPTIONS_GHC -Wno-missing-export-lists #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}

module TypeElab where

import           Syn (ExprTerm(..), Literal(..), PrimitiveType(..), Pattern(..)
                    , TypeTerm(..), TypeDescriptor(..), TypePattern(..))
import           Control.Monad.RWS (gets)
import           Control.Monad (mapAndUnzipM, zipWithM, forM, zipWithM_, forM_
                              , unless)
import           TypeUtils (TypeValue(..), TypeFailure(..), TypeCheckT, uplevel
                          , newVar, getCurrentLevel, putBorder, getBorder
                          , downlevel, setBorder)
import           Utils
import           Control.Monad.Error.Class (MonadError(throwError))
import           Data.Bool (bool)
import           Control.Applicative (Applicative(liftA2))
import qualified Data.Sequence as Seq
import           Control.Monad.State (evalState)
import           Control.Monad.Except (runExceptT)
import           Prelude hiding (exp)
import           Data.Functor.Identity
import Debug.Trace (traceM)

-- | Type Elaboration
elaborate :: String |-> TypeValue -- ^ Bindings
          -> ExprTerm             -- ^ Expression
          -> TypeCheckT m TypeValue
elaborate bindings = \case
  Lit l -> TVPrimitive
    <$> case l of
      LInt _    -> pure PrimInt
      LBool _   -> pure PrimBool
      LString _ -> pure PrimString
      LUnit     -> pure PrimUnit
  Var x -> case lookup x bindings of
    Just t  -> pure t
    Nothing -> throwError (UnboundVariable x)
  Tuple es -> TVTuple <$> mapM (elaborate bindings) es
  Record fs -> TVRecord <$> mapM (\(f, e) -> (f, ) <$> elaborate bindings e) fs
  Fun ps ret body -> do
    level <- uplevel
    (ts, concat -> bindings') <- mapAndUnzipM (inferPattern bindings) ps
    isPoly <- gets $ not . null . (!!! level)
    unless isPoly downlevel
    let bindings'' = bindings <> bindings'
    bodyT <- elaborate bindings'' body
    retT <- case ret of
      Just ret' -> do
        retT' <- elaborateType bindings'' ret'
        bodyT `isSubtypeOf` retT'
          >>= flip unless (throwError (BadConversion bodyT retT'))
        unify bodyT retT'
        pure retT'
      Nothing   -> pure bodyT
    pure $ bool (TVArrow ts retT) (TVLam ts level $ TVArrow ts retT) isPoly
  App f args -> do
    fT <- elaborate bindings f
    argsT <- mapM (elaborate bindings) args
    let aux = \case
          TVArrow ts ret -> do
            zipWithM_
              (\t input -> input `isSubtypeOf` t
               >>= flip unless (throwError (TypeMismatch input t)))
              ts
              argsT
            zipWithM_ unify ts argsT
            pure ret
          TVLam ts lvl tv -> do
            deducedSet <- concat <$> zipWithM (deduce lvl) ts argsT
            reduced <- reduce lvl (map snd (nubAndSortAssoc deducedSet)) tv
            aux reduced
          TVVar Flexible lvl idx -> do
            (TVVar Flexible lvl -> var) <- newVar lvl
            unify (TVVar Flexible lvl idx) (TVArrow argsT var)
            pure var
          _ -> throwError (TypeMismatch fT (TVArrow [] TVBot))
    aux fT
  App' f args -> do
    argsT <- mapM (elaborateType bindings) args
    fT <- elaborate bindings f
    case fT of
      TVLam ts lvl tv -> do
        deducedSet <- concat <$> zipWithM (deduce lvl) ts argsT
        reduce lvl (map snd (nubAndSortAssoc deducedSet)) tv
      _ -> throwError (NotApplicable fT)
  Proj e label -> do
    eT <- elaborate bindings e
    case eT of
      TVRecord fs -> case lookup label fs of
        Just t  -> pure t
        Nothing -> throwError (MissingField label)
      TVVar Flexible lvl _ -> do
        (TVVar Flexible lvl -> var) <- newVar lvl
        unify eT (TVRecord [(label, var)])
        pure var
      _ -> throwError (TypeMismatch eT (TVRecord []))
  Seq es -> last <$> mapM (elaborate bindings) es
  Let p e body -> do
    eT <- elaborate bindings e
    bindings' <- checkPattern bindings p eT
    elaborate (bindings <> bindings') body
  TypeAlias name Nothing t body -> do
    tv <- elaborateType bindings t
    elaborate (bindings <> [(name, tv)]) body
  TypeAlias name (Just tvars) t body -> do
    lvl <- uplevel
    (tvars', concat -> (bindings <>) -> bindings')
      <- mapAndUnzipM (inferTypePattern bindings) tvars
    tv <- elaborateType bindings' t
    elaborate (bindings <> [(name, TVLam tvars' lvl tv)]) body
  Forall tvars body -> do
    lvl <- uplevel
    (tvars', concat -> (<> bindings) -> bindings')
      <- mapAndUnzipM (inferTypePattern bindings) tvars
    tv <- elaborate bindings' body
    pure $ TVLam tvars' lvl tv
  If cond t f -> do
    condT <- elaborate bindings cond
    tT <- elaborate bindings t
    fT <- elaborate bindings f
    let boolT = TVPrimitive PrimBool
    -- The condition must be a boolean
    condT `isSubtypeOf` boolT
      >>= flip unless (throwError (TypeMismatch condT boolT))
    unify condT boolT
    -- The types of the branches must be the same
    liftA2 (&&) (tT `isSubtypeOf` fT) (fT `isSubtypeOf` tT)
      >>= flip unless (throwError (TypeMismatch tT fT))
    pure tT
  _ -> error "Not implemented"

elaborateType :: String |-> TypeValue -- ^ Bindings
              -> TypeTerm             -- ^ Type
              -> TypeCheckT m TypeValue
elaborateType bindings = \case
  TPrimitive p -> pure (TVPrimitive p)
  TVar x -> maybe (throwError (UnboundVariable x)) pure (lookup x bindings)
  TTuple ts -> TVTuple <$> mapM (elaborateType bindings) ts
  TRecord fs -> TVRecord
    <$> mapM (\(f, t) -> (f, ) <$> elaborateType bindings t) fs
  TArrow ts t -> TVArrow <$> mapM (elaborateType bindings) ts
    <*> elaborateType bindings t
  TLam tvars body -> do
    lvl <- uplevel
    is <- mapM (const (newVar lvl)) tvars
    let vars = TVVar Flexible lvl <$> is
        bindings' = bindings <> zip tvars vars
    TVLam vars lvl <$> elaborateType bindings' body
  TApp t ts -> do
    t' <- elaborateType bindings t
    ts' <- mapM (elaborateType bindings) ts
    case t' of
      TVLam tvars lvl body -> do
        deducedSet <- concat <$> zipWithM (deduce lvl) tvars ts'
        reduce lvl (map snd (nubAndSortAssoc deducedSet)) body
      _ -> throwError (NotApplicable t')
  TProj t l -> do
    t' <- elaborateType bindings t
    case t' of
      TVRecord fs -> case lookup l fs of
        Just t'' -> pure t''
        Nothing  -> throwError (MissingField l)
      _           -> throwError (NotProjectable t')
  _ -> error "Not implemented"

inferPattern :: String |-> TypeValue
             -> Pattern
             -> TypeCheckT m (TypeValue, String |-> TypeValue)
inferPattern env = \case
  PAtom x    -> do
    lvl <- getCurrentLevel
    i <- newVar lvl
    pure $ TVVar Flexible lvl i :@: [(x, TVVar Flexible lvl i)]
  PTuple ps  -> do
    (ts, bindings) <- mapAndUnzipM (inferPattern env) ps
    pure (TVTuple ts, concat bindings)
  PRecord fs -> do
    (ts, bindings) <- mapAndUnzipM (inferPattern env) (snd <$> fs)
    pure (TVRecord (zip (fst <$> fs) ts), concat bindings)
  PWildcard  -> do
    lvl <- getCurrentLevel
    i <- newVar lvl
    pure $ TVVar Flexible lvl i :@: []
  PAnnot p t -> do
    t' <- elaborateType env t
    bindings' <- checkPattern env p t'
    pure (t', bindings')
  PAs p x    -> do
    (t, bindings) <- inferPattern env p
    pure (t, (x, t):bindings)

checkPattern :: String |-> TypeValue
             -> Pattern
             -> TypeValue
             -> TypeCheckT m (String |-> TypeValue)
checkPattern env = curry
  $ \case
    (PAtom x, ty) -> pure [(x, ty)]
    (PTuple ps, TVTuple ts) -> do
      bindings <- zipWithM (checkPattern env) ps ts
      pure $ concat bindings
    (PRecord fs, TVRecord ts) -> do
      bindings <- forM fs
        $ \(f, p) -> do
          case lookup f ts of
            Just t  -> checkPattern env p t
            Nothing -> throwError (BadPattern p (TVRecord ts))
      pure $ concat bindings
    (PWildcard, _) -> pure []
    (PAnnot p t1, t2) -> do
      t1' <- elaborateType env t1
      t1' `isSubtypeOf` t2 >>= flip unless (throwError (TypeMismatch t1' t2))
      checkPattern env p t1'
    (p, v) -> throwError (BadPattern p v)

inferTypePattern :: String |-> TypeValue
                 -> TypePattern
                 -> TypeCheckT m (TypeValue, String |-> TypeValue)
inferTypePattern env = \case
  TPAtom td x -> do
    lvl <- getCurrentLevel
    traceM $ "inferTypePattern " ++ x ++ " level " ++ show lvl
    i <- newVar lvl
    pure $ TVVar td lvl i :@: [(x, TVVar td lvl i)]
  TPTuple ps  -> do
    (ts, bindings) <- mapAndUnzipM (inferTypePattern env) ps
    pure (TVTuple ts, concat bindings)
  TPRecord fs -> do
    (ts, bindings) <- mapAndUnzipM (inferTypePattern env) (snd <$> fs)
    pure (TVRecord (zip (fst <$> fs) ts), concat bindings)

unify :: TypeValue -> TypeValue -> TypeCheckT m ()
unify = curry
  $ \case
    (TVPrimitive p1, TVPrimitive p2)
      | p1 == p2 -> pure ()
    (TVVar td1 lvl1 idx1, TVVar td2 lvl2 idx2)
      | lvl1 <= lvl2 && td1 == Flexible
        -> putBorder lvl1 idx1 (Border TVTop (TVVar td2 lvl2 idx2))
      | lvl1 > lvl2 && td2 == Flexible
        -> putBorder lvl2 idx2 (Border (TVVar td1 lvl1 idx1) TVBot)
    (TVVar Flexible lvl idx, t) -> putBorder lvl idx (Border TVTop t)
    (t, TVVar Flexible lvl idx) -> putBorder lvl idx (Border t TVBot)
    (TVTuple ts1, TVTuple ts2)
      | length ts1 == length ts2 -> zipWithM_ unify ts1 ts2
    (TVRecord fs1, TVRecord fs2) -> forM_ fs1
      $ \(f, t1) -> case lookup f fs2 of
        Just t2 -> unify t1 t2
        Nothing -> throwError (MissingField f)
    (TVArrow ts1 t1, TVArrow ts2 t2)
      | length ts1 == length ts2 -> do
        zipWithM_ unify ts1 ts2
        unify t1 t2
    _ -> pure ()

-- | A `isSubtypeOf` B 
--   A is a subtype of B if A is more general than B
--   A can be substituted for B
--   TVBot is the most general type
--   TVTop is the most specific type
isSubtypeOf :: TypeValue -> TypeValue -> TypeCheckT m Bool
isSubtypeOf = curry
  $ \case
    (TVBot, _) -> pure True
    (_, TVTop) -> pure True
    (TVPrimitive p1, TVPrimitive p2) -> pure (p1 == p2)
    (TVLam _ _ tv, ty) -> isSubtypeOf tv ty
    (ty, TVLam _ _ tv) -> isSubtypeOf ty tv
    (TVVar _ lvl idx, TVVar _ lvl' idx') -> do
      border <- getBorder lvl idx
      border' <- getBorder lvl' idx'
      -- border is more general than border'
      -- top of border is more general than top of border'
      -- bot of border is less general than bot of border'
      fmap (all and)
        $ forM border
        $ \b -> forM border'
        $ \b' -> liftA2
          (&&)
          (isSubtypeOf (top b) (top b'))
          (isSubtypeOf (bot b') (bot b))
    (TVVar _ lvl idx, t) -> fmap and
      $ do
        borders <- getBorder lvl idx
        forM borders
          $ \border -> liftA2
            (&&)
            (isSubtypeOf (top border) t)
            (isSubtypeOf t (bot border))
    (t, TVVar _ lvl idx) -> fmap and
      $ do
        borders <- getBorder lvl idx
        forM borders
          $ \border -> liftA2
            (&&)
            (isSubtypeOf t (top border))
            (isSubtypeOf (bot border) t)
    (TVTuple ts1, TVTuple ts2)
      | length ts1 == length ts2 -> and <$> zipWithM isSubtypeOf ts1 ts2
    (TVRecord fs1, TVRecord fs2) -> fmap and <$> forM fs1
      $ \(f, t1) -> case lookup f fs2 of
        Just t2 -> isSubtypeOf t1 t2
        Nothing -> pure False
    (TVArrow ts1 t1, TVArrow ts2 t2)
      | length ts1 == length ts2 -> do
        ts <- zipWithM isSubtypeOf ts2 ts1
        t <- isSubtypeOf t1 t2
        pure (and ts && t)
    _ -> pure False

reduce :: Level -> [TypeValue] -> TypeValue -> TypeCheckT m TypeValue
reduce lvl ts = \case
  TVVar td lvl' idx -> do
    if lvl' == lvl
      then
        -- If the variable is in the current level, we can reduce it
        maybe
          (throwError $ TypeVariableOutOfScope lvl idx)
          pure
          (lookup idx (zip [0 ..] ts))
      else
        -- Otherwise, we need to update the border
        do
          border <- getBorder lvl' idx
          border' <- forM border
            $ \(Border top' bot') -> do
              top'' <- reduce lvl ts top'
              bot'' <- reduce lvl ts bot'
              pure $ Border top'' bot''
          setBorder lvl' idx border'
          pure (TVVar td lvl' idx)
  TVTuple ts' -> TVTuple <$> zipWithM (reduce lvl) (repeat ts) ts'
  TVRecord fs -> TVRecord <$> mapM (\(f, t) -> (f, ) <$> reduce lvl ts t) fs
  TVArrow ts' t -> TVArrow <$> mapM (reduce lvl ts) ts' <*> reduce lvl ts t
  TVLam ts' lvl' tv
    -> TVLam <$> mapM (reduce lvl ts) ts' <*> pure lvl' <*> reduce lvl ts tv
  t -> pure t

deduce :: Level -> TypeValue -> TypeValue -> TypeCheckT m [(Int, TypeValue)]
deduce lvl = curry
  \case
    -- (TVLam _ _ tv, ty) -> deduce lvl tv ty
    -- (ty, TVLam _ _ tv) -> deduce lvl ty tv
    (tv@(TVVar _ lvl' idx), t) -> do
      unlessM (isSubtypeOf t tv) $ throwError (TypeMismatch t tv)
      border <- getBorder lvl idx
      tys <- fmap concat
        $ forM border
        $ \(Border top' bot') -> do
          top'' <- deduce lvl top' t
          bot'' <- deduce lvl t bot'
          pure $ top'' ++ bot''
      pure $ bool [] [(idx, t)] (lvl == lvl') ++ tys
    (t, tv@(TVVar _ lvl' idx)) -> do
      unlessM (isSubtypeOf tv t) $ throwError (TypeMismatch tv t)
      border <- getBorder lvl idx
      tys <- fmap concat
        $ forM border
        $ \(Border top' bot') -> do
          top'' <- deduce lvl t top'
          bot'' <- deduce lvl bot' t
          pure $ top'' ++ bot''
      pure $ bool [] [(idx, t)] (lvl == lvl') ++ tys
    (TVTuple ts1, TVTuple ts2)
      | length ts1 == length ts2 -> concat <$> zipWithM (deduce lvl) ts1 ts2
    (TVRecord fs1, TVRecord fs2) -> fmap concat
      $ forM fs2
      $ \(f, t1) -> case lookup f fs1 of
        Just t2 -> deduce lvl t1 t2
        Nothing -> throwError (MissingField f)
    (TVArrow ts1 t1, TVArrow ts2 t2) -> do
      ts <- concat <$> zipWithM (deduce lvl) ts2 ts1
      t <- deduce lvl t1 t2
      pure $ ts ++ t
    (a, b) -> unlessM (isSubtypeOf b a) (throwError (TypeMismatch a b))
      >> pure []

topmost :: TypeValue -> TypeValue -> TypeCheckT m TypeValue
topmost (TVRecord fs1) (TVRecord fs2) = TVRecord
  <$> sequence
    (do
       (l1, t1) <- fs1
       (l2, t2) <- fs2
       if l1 == l2
         then pure ((l1, ) <$> topmost t1 t2)
         else pure <$> [(l1, t1), (l2, t2)])
topmost (TVTuple ts1) (TVTuple ts2) = TVTuple <$> zipWithM topmost ts1 ts2
topmost (TVArrow ts1 t1) (TVArrow ts2 t2) =
  TVArrow <$> zipWithM botmost ts1 ts2 <*> topmost t1 t2
topmost a b = isSubtypeOf a b
  >>= \case
    True  -> pure b
    False -> isSubtypeOf b a
      >>= \case
        True  -> pure a
        False -> pure TVTop

botmost :: TypeValue -> TypeValue -> TypeCheckT m TypeValue
botmost (TVRecord fs1) (TVRecord fs2) =
  let flds = do
        (l1, t1) <- fs1
        (l2, t2) <- fs2
        if l1 == l2
          then pure ((l1, ) <$> botmost t1 t2)
          else []
  in if null flds
     then pure TVBot
     else TVRecord <$> sequence flds
botmost (TVTuple ts1) (TVTuple ts2) = TVTuple <$> zipWithM botmost ts1 ts2
botmost (TVArrow ts1 t1) (TVArrow ts2 t2) =
  TVArrow <$> zipWithM topmost ts1 ts2 <*> botmost t1 t2
botmost a b = isSubtypeOf a b
  >>= \case
    True  -> pure a
    False -> isSubtypeOf b a
      >>= \case
        True  -> pure b
        False -> pure TVBot

testTypeCheck :: ExprTerm -> Either TypeFailure TypeValue
testTypeCheck exp = evalState (runExceptT m) Seq.empty
  where
    m :: TypeCheckT Identity TypeValue
    m = elaborate [] exp