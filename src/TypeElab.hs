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
                    , TypeTerm(..))
import           Control.Monad.RWS (MonadState(..), gets)
import           Control.Monad (mapAndUnzipM, zipWithM, forM, zipWithM_, forM_
                              , unless)
import           TypeUtils (TypeValue(..), TypeFailure(..), Border(Border)
                          , TypeCheckT, uplevel, newVar, TClosure(TClosure)
                          , getCurrentLevel, putBorder, getBorder, top, bot
                          , save, downlevel, setBorder)
import           Utils
import           Control.Monad.Error.Class (MonadError(throwError))
import           Data.Bool (bool)
import           Control.Applicative (Applicative(liftA2))
import qualified Data.Sequence as Seq
import           Control.Monad.State (evalState)
import           Control.Monad.Except (runExceptT)
import           Prelude hiding (exp)
import           Debug.Trace (traceM)
import           Data.Functor.Identity

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
    (ts, concat -> bindings') <- mapAndUnzipM inferPattern ps
    isPoly <- gets $ not . null . (!!! level)
    unless isPoly downlevel
    save
      do
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
        env <- get
        pure
          $ bool
            (TVArrow ts retT)
            (TVLam ts (TClosure (TVArrow ts retT) env))
            isPoly
  App f args -> do
    fT <- elaborate bindings f
    let aux = \case
          TVArrow ts ret -> do
            argsT <- mapM (elaborate bindings) args
            zipWithM_
              (\t input -> input `isSubtypeOf` t
               >>= flip unless (throwError (TypeMismatch input t)))
              ts
              argsT
            zipWithM_ unify ts argsT
            pure ret
          TVLam ts cls@(TClosure _ env) -> save
            do
              put env
              argsT <- mapM (elaborate bindings) args
              deducedSet <- concat
                <$> zipWithM (deduce (Seq.length env - 1)) ts argsT
              traceM
                $ "ts = "
                ++ show ts
                ++ ", argsT = "
                ++ show argsT
                ++ ", deducedSet = "
                ++ show deducedSet
              reduced <- cls $$ map snd (nubAndSortAssoc deducedSet)
              aux reduced
          _ -> throwError (TypeMismatch fT (TVArrow [] TVBot))
    aux fT
  Proj e label -> do
    eT <- elaborate bindings e
    case eT of
      TVRecord fs -> case lookup label fs of
        Just t  -> pure t
        Nothing -> throwError (MissingField label)
      TVVar lvl _ -> do
        (TVVar lvl -> var) <- newVar lvl
        unify eT (TVRecord [(label, var)])
        pure var
      _           -> throwError (TypeMismatch eT (TVRecord []))
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
    let vars = TVVar lvl <$> is
        bindings' = bindings <> zip tvars vars
    body' <- elaborateType bindings' body
    TVLam vars . TClosure body' <$> get
  _ -> error "Not implemented"

inferPattern :: Pattern -> TypeCheckT m (TypeValue, String |-> TypeValue)
inferPattern = \case
  PAtom x    -> do
    lvl <- getCurrentLevel
    i <- newVar lvl
    pure $ TVVar lvl i :@: [(x, TVVar lvl i)]
  PTuple ps  -> do
    (ts, bindings) <- mapAndUnzipM inferPattern ps
    pure (TVTuple ts, concat bindings)
  PRecord fs -> do
    (ts, bindings) <- mapAndUnzipM inferPattern (snd <$> fs)
    pure (TVRecord (zip (fst <$> fs) ts), concat bindings)
  PWildcard  -> do
    lvl <- getCurrentLevel
    i <- newVar lvl
    pure $ TVVar lvl i :@: []
  PAnnot p t -> do
    t' <- elaborateType [] t
    bindings' <- checkPattern p t'
    pure (t', bindings')

checkPattern :: Pattern -> TypeValue -> TypeCheckT m (String |-> TypeValue)
checkPattern = curry
  $ \case
    (PAtom x, ty) -> pure [(x, ty)]
    (PTuple ps, TVTuple ts) -> do
      bindings <- zipWithM checkPattern ps ts
      pure $ concat bindings
    (PRecord fs, TVRecord ts) -> do
      bindings <- forM fs
        $ \(f, p) -> do
          case lookup f ts of
            Just t  -> checkPattern p t
            Nothing -> throwError (BadPattern p (TVRecord ts))
      pure $ concat bindings
    (PWildcard, _) -> pure []
    (PAnnot _p _t, _) -> error "Not implemented"
    (p, v) -> throwError (BadPattern p v)

unify :: TypeValue -> TypeValue -> TypeCheckT m ()
unify = curry
  $ \case
    (TVPrimitive p1, TVPrimitive p2)
      | p1 == p2 -> pure ()
    (TVVar lvl1 idx1, TVVar lvl2 idx2)
      | lvl1 <= lvl2 -> putBorder lvl1 idx1 (Border TVTop (TVVar lvl2 idx2))
      | lvl1 > lvl2 -> putBorder lvl2 idx2 (Border (TVVar lvl1 idx1) TVBot)
    (TVVar lvl idx, t) -> putBorder lvl idx (Border TVTop t)
    (t, TVVar lvl idx) -> putBorder lvl idx (Border t TVBot)
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
    _ -> error "Not implemented"

-- | A `isSubtypeOf` B 
--   A is a subtype of B if A is more general than B
--   A can be substituted for B
isSubtypeOf :: TypeValue -> TypeValue -> TypeCheckT m Bool
isSubtypeOf = curry
  $ \case
    (TVBot, _) -> pure True
    (_, TVTop) -> pure True
    (TVPrimitive p1, TVPrimitive p2) -> pure (p1 == p2)
    (TVVar lvl idx, TVVar lvl' idx') -> do
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
    (TVVar lvl idx, t) -> fmap and
      $ do
        borders <- getBorder lvl idx
        forM borders
          $ \border -> liftA2
            (&&)
            (isSubtypeOf (top border) t)
            (isSubtypeOf t (bot border))
    (t, TVVar lvl idx) -> fmap and
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
    (TVLam _ (TClosure t env), ty) -> save $ put env >> isSubtypeOf t ty
    (ty, TVLam _ (TClosure t env)) -> save $ put env >> isSubtypeOf ty t
    _ -> pure False

($$) :: TClosure -> [TypeValue] -> TypeCheckT m TypeValue
TClosure t env $$ ts = put env >> reduce ts t

reduce :: [TypeValue] -> TypeValue -> TypeCheckT m TypeValue
reduce ts = \case
  TVVar lvl idx -> do
    lvl' <- getCurrentLevel
    if lvl' == lvl
      then 
        -- If the variable is in the current level, we can reduce it
        pure (ts !! idx)
      else 
        -- Otherwise, we need to update the border
        do
          border <- getBorder lvl idx
          border' <- forM border
            $ \(Border top' bot') -> do
              top'' <- reduce ts top'
              bot'' <- reduce ts bot'
              pure $ Border top'' bot''
          setBorder lvl idx border'
          pure (TVVar lvl idx)
  TVTuple ts' -> TVTuple <$> zipWithM reduce (repeat ts) ts'
  TVRecord fs -> TVRecord <$> mapM (\(f, t) -> (f, ) <$> reduce ts t) fs
  TVArrow ts' t -> TVArrow <$> mapM (reduce ts) ts' <*> reduce ts t
  TVLam ts' (TClosure t env) -> TVLam ts'
    <$> (TClosure <$> reduce ts t <*> pure env)
  t -> pure t

deduce :: Level -> TypeValue -> TypeValue -> TypeCheckT m [(Int, TypeValue)]
deduce lvl = curry
  \case
    (TVVar lvl' idx, t) -> do
      unlessM (isSubtypeOf t (TVVar lvl idx))
        $ throwError (TypeMismatch t (TVVar lvl idx))
      border <- getBorder lvl idx
      tys <- fmap concat
        $ forM border
        $ \(Border top' bot') -> do
          top'' <- deduce lvl top' t
          bot'' <- deduce lvl t bot'
          pure $ top'' ++ bot''
      pure $ bool [] [(idx, t)] (lvl == lvl') ++ tys
    (TVTuple ts1, TVTuple ts2)
      | length ts1 == length ts2 -> concat <$> zipWithM (deduce lvl) ts1 ts2
    (TVRecord fs1, TVRecord fs2) -> fmap concat
      $ forM fs1
      $ \(f, t1) -> case lookup f fs2 of
        Just t2 -> deduce lvl t1 t2
        Nothing -> throwError (MissingField f)
    (a, b) -> unlessM (isSubtypeOf a b) (throwError (TypeMismatch a b))
      >> pure []

testTypeCheck :: ExprTerm -> Either TypeFailure TypeValue
testTypeCheck exp = evalState (runExceptT m) Seq.empty
  where
    m :: TypeCheckT Identity TypeValue
    m = elaborate [] exp