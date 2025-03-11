{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module TypeElab where

import Control.Applicative (Applicative (liftA2))
import Control.Arrow (second)
import Control.Monad
  ( foldM,
    forM,
    forM_,
    mapAndUnzipM,
    unless,
    zipWithM,
    zipWithM_,
  )
import Control.Monad.Error.Class (MonadError (..))
import Control.Monad.Identity (Identity (runIdentity))
import Control.Monad.RWS (gets)
import Data.Bool (bool)
import Data.Functor (($>))
import Debug.Trace (traceM)
import Pretty (Color (..), Pretty, RawStr, freshGreek, render, txt, (#>))
import Syn
  ( ExprTerm (..),
    ExprTerm',
    Literal (..),
    Pattern (..),
    Pattern',
    PrimitiveType (..),
    TypeDescriptor (..),
    TypePattern (..),
    TypePattern',
    TypeTerm (..),
    TypeTerm',
  )
import TypePretty
import TypeUtils hiding (Border)
import Utils hiding (info)
import Prelude hiding (exp)

-- | Type Elaboration
elaborate ::
  -- | Bindings
  String |-> TypeValue' ->
  -- | Expression
  ExprTerm' ->
  TypeCheckT m TypeValue'
elaborate bindings fiExp = diagnose id $ forM fiExp $ \case
  Lit l ->
    TVPrimitive
      <$> case l of
        LInt _ -> pure PrimInt
        LBool _ -> pure PrimBool
        LString _ -> pure PrimString
        LUnit -> pure PrimUnit
  Var x -> case lookup x bindings of
    Just t -> pure (val t)
    Nothing -> throwError (info :?> UnboundVariable x)
  Tuple es -> TVTuple <$> mapM (elaborate bindings) es
  Record fs -> TVRecord <$> mapM (\(f, e) -> (f,) <$> elaborate bindings e) fs
  Fun ps ret body -> do
    level <- uplevel
    (ts, bindings') <- mapAndUnzipM (inferPattern bindings) ps
    isPoly <- gets' $ not . null . (!!! level)
    unless isPoly downlevel
    let bindings'' = bindings ++ concat bindings'
    saveScope (fi body) bindings''
    bodyT <- elaborate bindings'' body
    retT <- case ret of
      Just ret' -> do
        retT' <- elaborateType bindings'' ret'
        bodyT `isSubtypeOf` retT'
          >>= flip unless (throwError (info :?> BadConversion bodyT retT'))
        unify bodyT retT'
        pure retT'
      Nothing -> pure bodyT
    pure $ bool (TVArrow ts retT) (TVLam ts level $ info :?> TVArrow ts retT) isPoly
  App f args -> do
    fT <- elaborate bindings f
    argsT <- mapM (elaborate bindings) args
    let aux = \case
          _ :?> TVArrow ts ret -> do
            zipWithM_ unify argsT ts
            zipWithM_
              ( \t input ->
                  input `isSubtypeOf` t
                    >>= flip unless (throwError (fi input :?> TypeMismatch input t))
              )
              ts
              argsT
            pure ret
          _ :?> TVLam ts lvl tv -> do
            deducedSet <- concat <$> zipWithM (deduce lvl) ts argsT
            reduced <- reduce lvl (map snd (nubAndSortAssoc deducedSet)) tv
            aux reduced
          i :?> TVVar Flexible lvl idx -> do
            ((i :?>) . TVVar Flexible lvl -> var) <- newVar lvl
            unify (i :?> TVVar Flexible lvl idx) (i :?> TVArrow argsT var)
            pure var
          i :?> tv -> throwError (i :?> NotApplicable (i :?> tv))
          _ -> error "Cannot happen"
    val <$> aux fT
  App' f args -> do
    argsT <- mapM (elaborateType bindings) args
    fT <- elaborate bindings f
    case fT of
      _ :?> TVLam ts lvl tv -> do
        deducedSet <- concat <$> zipWithM (deduce lvl) ts argsT
        val <$> reduce lvl (map snd (nubAndSortAssoc deducedSet)) tv
      _ -> throwError (fi f :?> NotApplicable fT)
  Proj e label -> do
    eT <- elaborate bindings e
    case eT of
      _ :?> TVRecord fs -> case lookup label fs of
        Just t -> pure $ val t
        Nothing -> throwError (info :?> MissingField label)
      i :?> TVVar Flexible lvl _ -> do
        (TVVar Flexible lvl -> var) <- newVar lvl
        unify eT (i :?> TVRecord [(label, i :?> var)])
        pure var
      _ -> throwError (info :?> NotProjectable eT)
  Seq [] -> pure $ TVPrimitive PrimUnit
  Seq es -> val . last <$> mapM (elaborate bindings) es
  Let p e body -> do
    eT <- elaborate bindings e
    bindings' <- checkPattern bindings p eT
    let bindings'' = bindings ++ bindings'
    saveScope (fi body) bindings''
    val <$> elaborate bindings'' body
  TypeAlias name Nothing t body -> do
    tv <- elaborateType bindings t
    let bindings' = bindings ++ [(name, tv)]
    saveScope (fi body) bindings'
    val <$> elaborate bindings' body
  TypeAlias name (Just tvars) t body -> do
    lvl <- uplevel
    (tvars', concat -> (bindings ++) -> bindings') <-
      mapAndUnzipM (inferTypePattern bindings) tvars
    tv <- elaborateType bindings' t
    let bindings'' = bindings' ++ [(name, info :?> TVLam tvars' lvl tv)]
    saveScope (fi body) bindings''
    val <$> elaborate bindings'' body
  Forall tvars body -> do
    lvl <- uplevel
    (tvars', concat -> (bindings ++) -> bindings') <-
      mapAndUnzipM (inferTypePattern bindings) tvars
    saveScope (fi body) bindings'
    tv <- elaborate bindings' body
    pure $ TVLam tvars' lvl tv
  If cond t f -> do
    condT <- elaborate bindings cond
    tT <- elaborate bindings t
    fT <- elaborate bindings f
    let boolT = info :?> TVPrimitive PrimBool
    -- The condition must be a boolean
    condT `isSubtypeOf` boolT
      >>= flip unless (throwError (fi condT :?> TypeMismatch condT boolT))
    unify condT boolT
    -- The types of the branches must be the same
    liftA2 (&&) (tT `isSubtypeOf` fT) (fT `isSubtypeOf` tT)
      >>= flip unless (throwError (fi fT <> fi tT :?> TypeMismatch tT fT))
    pure $ val tT
  Keyword "absurd" (Right ty) -> val <$> elaborateType bindings ty
  _ -> error "Not implemented"
  where
    info = fi fiExp

elaborateType ::
  -- | Bindings
  String |-> TypeValue' ->
  -- | Type
  TypeTerm' ->
  TypeCheckT m TypeValue'
elaborateType bindings fiTy = diagnose id $ forM fiTy $ \case
  TPrimitive p -> pure (TVPrimitive p)
  TVar x ->
    maybe
      (throwError (named info x :?> UnboundVariable x))
      (pure . val)
      (lookup x bindings)
  TTuple ts -> TVTuple <$> mapM (elaborateType bindings) ts
  TRecord fs ->
    TVRecord
      <$> mapM (\(f, t) -> (f,) <$> elaborateType bindings t) fs
  TArrow ts t ->
    TVArrow
      <$> mapM (elaborateType bindings) ts
      <*> elaborateType bindings t
  TLam tvars body -> do
    lvl <- uplevel
    is <- mapM (const (newVar lvl)) tvars
    let vars = WithFI info . TVVar Flexible lvl <$> is
        bindings' = bindings ++ zip tvars vars
    TVLam vars lvl <$> elaborateType bindings' body
  TApp t ts -> do
    t' <- elaborateType bindings t
    ts' <- mapM (elaborateType bindings) ts
    case t' of
      _ :?> TVLam tvars lvl body -> do
        deducedSet <- concat <$> zipWithM (deduce lvl) tvars ts'
        val <$> reduce lvl (map snd (nubAndSortAssoc deducedSet)) body
      _ -> throwError (fi t' :?> NotApplicable t')
  TProj t l -> do
    t' <- elaborateType bindings t
    case t' of
      _ :?> TVRecord fs -> case lookup l fs of
        Just t'' -> pure $ val t''
        Nothing -> throwError (info :?> MissingField l)
      _ -> throwError (fi t' :?> NotProjectable t')
  _ -> error "Not implemented"
  where
    info = fi fiTy

inferPattern ::
  String |-> TypeValue' ->
  Pattern' ->
  TypeCheckT m (TypeValue', String |-> TypeValue')
inferPattern env (WithFI info _p) = diagnose fst $ case _p of
  PAtom x -> do
    lvl <- getCurrentLevel
    i <- newVar lvl
    pure (info :?> TVVar Flexible lvl i, [(x, info :?> TVVar Flexible lvl i)])
  PTuple ps -> do
    (ts, bindings) <- mapAndUnzipM (inferPattern env) ps
    pure (info :?> TVTuple ts, concat bindings)
  PRecord fs -> do
    (ts, bindings) <- mapAndUnzipM (inferPattern env) (snd <$> fs)
    pure (info :?> TVRecord (zip (fst <$> fs) ts), concat bindings)
  PWildcard -> do
    lvl <- getCurrentLevel
    i <- newVar lvl
    pure $ info :?> TVVar Flexible lvl i :@: []
  PAnnot p t -> do
    t' <- elaborateType env t
    bindings' <- checkPattern env p t'
    pure (t', bindings')
  PAs p x -> do
    (t, bindings) <- inferPattern env p
    pure (t, (x, t) : bindings)

checkPattern ::
  String |-> TypeValue' ->
  Pattern' ->
  TypeValue' ->
  TypeCheckT m (String |-> TypeValue')
checkPattern env _p tv = case (val _p, tv) of
  (PAtom x, ty) -> pure [(x, ty)]
  (PTuple ps, _ :?> TVTuple ts) -> do
    bindings <- zipWithM (checkPattern env) ps ts
    pure $ concat bindings
  (PRecord fs, i :?> TVRecord ts) -> do
    bindings <- forM fs $
      \(f, p) -> do
        case lookup f ts of
          Just t -> checkPattern env p t
          Nothing -> throwError (fi _p :?> BadPattern p (i :?> TVRecord ts))
    pure $ concat bindings
  (PWildcard, _) -> pure []
  (PAnnot p t1, t2) -> do
    t1' <- elaborateType env t1
    t1' `isSubtypeOf` t2 >>= flip unless (throwError (t2 $> TypeMismatch t1' t2))
    checkPattern env p t1'
  (_, v) -> throwError (fi _p :?> BadPattern _p v)

inferTypePattern ::
  String |-> TypeValue' ->
  TypePattern' ->
  TypeCheckT m (TypeValue', String |-> TypeValue')
inferTypePattern env (WithFI info _p) = case _p of
  TPAtom td x -> do
    lvl <- getCurrentLevel
    i <- newVar lvl
    pure (info :?> TVVar td lvl i, [(x, info :?> TVVar td lvl i)])
  TPTuple ps -> do
    (ts, bindings) <- mapAndUnzipM (inferTypePattern env) ps
    pure (info :?> TVTuple ts, concat bindings)
  TPRecord fs -> do
    (ts, bindings) <- mapAndUnzipM (inferTypePattern env) (snd <$> fs)
    pure (info :?> TVRecord (zip (fst <$> fs) ts), concat bindings)

unify :: TypeValue' -> TypeValue' -> TypeCheckT m ()
unify (WithFI _ tv1) (WithFI _ tv2) = case (tv1, tv2) of
  (TVPrimitive p1, TVPrimitive p2)
    | p1 == p2 -> pure ()
  (TVVar td1 lvl1 idx1, TVVar td2 lvl2 idx2)
    | lvl1 <= lvl2 && td1 == Flexible ->
        putBorder lvl1 idx1 (Border TVTop (TVVar td2 lvl2 idx2))
    | lvl1 > lvl2 && td2 == Flexible ->
        putBorder lvl2 idx2 (Border (TVVar td1 lvl1 idx1) TVBot)
  (TVVar Flexible lvl idx, t) -> putBorder lvl idx (Border TVTop t)
  (t, TVVar Flexible lvl idx) -> putBorder lvl idx (Border t TVBot)
  (TVTuple ts1, TVTuple ts2)
    | length ts1 == length ts2 -> zipWithM_ unify ts1 ts2
  (TVRecord fs1, TVRecord fs2) -> forM_ fs1 $
    \(f, t1) -> case lookup f fs2 of
      Just t2 -> unify t1 t2
      Nothing -> error "Never happens"
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
isSubtypeOf :: TypeValue' -> TypeValue' -> TypeCheckT m Bool
isSubtypeOf tv1 tv2 = case (val tv1, val tv2) of
  (TVBot, _) -> pure True
  (_, TVTop) -> pure True
  (TVPrimitive p1, TVPrimitive p2) -> pure (p1 == p2)
  (TVLam _ _ tv, _) -> isSubtypeOf tv tv2
  (_, TVLam _ _ tv) -> isSubtypeOf tv1 tv
  (TVVar _ lvl idx, TVVar _ lvl' idx') -> do
    border <- getBorder lvl idx
    border' <- getBorder lvl' idx'
    -- border is more general than border'
    -- top of border is more general than top of border'
    -- bot of border is less general than bot of border'
    fmap (all and) $
      forM border $
        \b -> forM border' $
          \b' ->
            liftA2
              (&&)
              (isSubtypeOf (fi tv1 :?> top b) (fi tv2 :?> top b'))
              (isSubtypeOf (fi tv2 :?> bot b') (fi tv1 :?> bot b))
  (TVVar _ lvl idx, _) -> fmap and $
    do
      borders <- getBorder lvl idx
      forM borders $
        \border ->
          liftA2
            (&&)
            (isSubtypeOf tv2 (fi tv1 :?> top border))
            (isSubtypeOf (fi tv1 :?> bot border) tv2)
  (_, TVVar _ lvl idx) -> fmap and $
    do
      borders <- getBorder lvl idx
      forM borders $
        \border ->
          liftA2
            (&&)
            (isSubtypeOf (fi tv2 :?> top border) tv1)
            (isSubtypeOf tv1 (fi tv2 :?> bot border))
  (TVTuple ts1, TVTuple ts2)
    | length ts1 == length ts2 -> and <$> zipWithM isSubtypeOf ts1 ts2
  (TVRecord fs1, TVRecord fs2) -> fmap and <$> forM fs1 $
    \(f, t1) -> case lookup f fs2 of
      Just t2 -> isSubtypeOf t1 t2
      Nothing -> pure False
  (TVArrow ts1 t1, TVArrow ts2 t2)
    | length ts1 == length ts2 -> do
        ts <- zipWithM isSubtypeOf ts2 ts1
        t <- isSubtypeOf t1 t2
        pure (and ts && t)
  _ -> pure False

reduce :: Level -> [TypeValue'] -> TypeValue' -> TypeCheckT m TypeValue'
reduce lvl ts _tv = forM _tv \case
  TVVar td lvl' idx -> do
    if lvl' == lvl
      then -- If the variable is in the current level, we can reduce it

        maybe
          (throwError (fi _tv :?> TypeVariableOutOfScope lvl idx))
          pure
          (lookup idx (zip [0 ..] (val <$> ts)))
      else -- Otherwise, we need to update the border
      do
        border <- getBorder lvl' idx
        border' <- forM border $
          \(Border top' bot') -> do
            top'' <- val <$> reduce lvl ts (fi _tv :?> top')
            bot'' <- val <$> reduce lvl ts (fi _tv :?> bot')
            pure $ Border top'' bot''
        setBorder lvl' idx border'
        pure $ TVVar td lvl' idx
  TVTuple ts' -> TVTuple <$> zipWithM (reduce lvl) (repeat ts) ts'
  TVRecord fs -> TVRecord <$> mapM (\(f, t) -> (f,) <$> reduce lvl ts t) fs
  TVArrow ts' t -> TVArrow <$> mapM (reduce lvl ts) ts' <*> reduce lvl ts t
  TVLam ts' lvl' tv ->
    TVLam <$> mapM (reduce lvl ts) ts' <*> pure lvl' <*> reduce lvl ts tv
  t -> pure t

deduce :: Level -> TypeValue' -> TypeValue' -> TypeCheckT m [(Int, TypeValue')]
deduce lvl _l _r = case (val _l, val _r) of
  -- (TVLam _ _ tv, ty) -> deduce lvl tv ty
  -- (ty, TVLam _ _ tv) -> deduce lvl ty tv
  (TVVar _ lvl' idx, _) -> do
    unlessM (isSubtypeOf _l _r) $ throwError (fi _r :?> TypeMismatch _l _r)
    border <- getBorder lvl idx
    tys <- fmap concat $
      forM border $
        \(Border top' bot') -> do
          top'' <- deduce lvl (fi _l :?> top') _r
          bot'' <- deduce lvl _r (fi _l :?> bot')
          pure $ top'' ++ bot''
    pure $ bool [] [(idx, _r)] (lvl == lvl') ++ tys
  (_, TVVar _ lvl' idx) -> do
    unlessM (isSubtypeOf _l _r) $ throwError (fi _l :?> TypeMismatch _l _r)
    border <- getBorder lvl idx
    tys <- fmap concat $
      forM border $
        \(Border top' bot') -> do
          top'' <- deduce lvl _l (fi _r :?> top')
          bot'' <- deduce lvl (fi _r :?> bot') _l
          pure $ top'' ++ bot''
    pure $ bool [] [(idx, _l)] (lvl == lvl') ++ tys
  (TVTuple ts1, TVTuple ts2)
    | length ts1 == length ts2 -> concat <$> zipWithM (deduce lvl) ts1 ts2
  (TVRecord fs1, TVRecord fs2) -> fmap concat $
    forM fs2 $
      \(f, t1) -> case lookup f fs1 of
        Just t2 -> deduce lvl t1 t2
        Nothing -> throwError (fi _l :?> MissingField f)
  (TVArrow ts1 t1, TVArrow ts2 t2) -> do
    ts <- concat <$> zipWithM (deduce lvl) ts2 ts1
    t <- deduce lvl t1 t2
    pure $ ts ++ t
  _ ->
    unlessM (isSubtypeOf _r _l) (throwError (fi _r :?> TypeMismatch _l _r))
      >> pure []

topmost :: TypeValue' -> TypeValue' -> TypeCheckT m TypeValue'
topmost (_ :?> TVRecord fs1) (i :?> TVRecord fs2) =
  fmap (i :?>) $
    TVRecord
      <$> sequence
        ( do
            (l1, t1) <- fs1
            (l2, t2) <- fs2
            if l1 == l2
              then pure ((l1,) <$> topmost t1 t2)
              else pure <$> [(l1, t1), (l2, t2)]
        )
topmost (_ :?> TVTuple ts1) (i :?> TVTuple ts2) = fmap (i :?>) $ TVTuple <$> zipWithM topmost ts1 ts2
topmost (_ :?> TVArrow ts1 t1) (i :?> TVArrow ts2 t2) =
  fmap (i :?>) $
    TVArrow <$> zipWithM botmost ts1 ts2 <*> topmost t1 t2
topmost a b =
  isSubtypeOf a b
    >>= \case
      True -> pure b
      False ->
        isSubtypeOf b a
          >>= \case
            True -> pure a
            False -> pure (fi a :?> TVTop)

botmost :: TypeValue' -> TypeValue' -> TypeCheckT m TypeValue'
botmost (_ :?> TVRecord fs1) (i :?> TVRecord fs2) =
  fmap (i :?>) $
    TVRecord
      <$> sequence
        ( do
            (l1, t1) <- fs1
            (l2, t2) <- fs2
            if l1 == l2
              then pure ((l1,) <$> botmost t1 t2)
              else pure <$> [(l1, t1), (l2, t2)]
        )
botmost (_ :?> TVTuple ts1) (i :?> TVTuple ts2) = fmap (i :?>) $ TVTuple <$> zipWithM botmost ts1 ts2
botmost (_ :?> TVArrow ts1 t1) (i :?> TVArrow ts2 t2) =
  fmap (i :?>) $
    TVArrow <$> zipWithM topmost ts1 ts2 <*> botmost t1 t2
botmost a b =
  isSubtypeOf a b
    >>= \case
      True -> pure a
      False ->
        isSubtypeOf b a
          >>= \case
            True -> pure b
            False -> pure (fi b :?> TVBot)

-- Pretty Printing

quoteError :: WithFI TypeFailure -> TypeCheckT m (WithFI $ Pretty (Int, Int) RawStr)
quoteError fiTy = forM fiTy $ \case
  UndefinedType tv -> txt "Undefined type: " <+ q tv
  UnboundVariable s -> txt "Unbound variable: " <+> txt s
  TypeMismatch tv1 tv2 ->
    txt "Type mismatch: " <+ q tv1 +> txt " and " <<>> q tv2
  BadPattern _ tv -> txt "Bad pattern with type " <+ q tv
  BadConversion tv1 tv2 ->
    txt "Bad conversion from " <+ q tv1 <<>> txt " to " <+ q tv2
  MissingField s -> pure $ txt "Missing field: " <> txt s
  TooManyFields -> pure $ txt "Too many fields"
  TypeVariableOutOfScope lvl idx ->
    pure $
      txt "Type variable out of scope: "
        <> Italics Green #> freshGreek (lvl, idx)
  NotApplicable tv -> txt "Not applicable: " <+ q tv
  NotProjectable tv -> txt "Not projectable: " <+ q tv
  where
    q = (pretty0 <$>) . quoteType

quoteType :: TypeValue' -> TypeCheckT m TypePtty'
quoteType fiTy = forM fiTy $ \case
  TVTop -> pure PttyTop
  TVBot -> pure PttyBot
  TVPrimitive pt -> pure $ PttyPrimitive pt
  TVVar td lvl idx -> do
    border <- getBorder lvl idx
    normed <- normalizeBorder border
    pure $ PttyVar normed td lvl idx
  TVArrow args ret ->
    PttyArrow
      <$> mapM quoteType args
      <*> quoteType ret
  TVTuple elems -> PttyTuple <$> mapM quoteType elems
  TVRecord fields ->
    PttyRecord
      <$> mapM (secondM quoteType) fields
  TVLam vars lvl body ->
    PttyLam . concat
      <$> mapM (extractVars lvl) vars
      <*> quoteType body
  where
    secondM f (a, b) = (a,) <$> f b

normalizeBorder :: [Border TypeValue] -> TypeCheckT m BorderPtty
normalizeBorder border = do
  let tops = map top border
      bots = map bot border
  -- The bottomost type of the tops
  top' <- foldM botmost (fiEmpty TVTop) (fiEmpty <$> tops) >>= quoteType
  -- The topmost type of the bottoms
  bot' <- foldM topmost (fiEmpty TVBot) (fiEmpty <$> bots) >>= quoteType
  pure $ Border top' bot'

extractVars ::
  Level -> TypeValue' -> TypeCheckT m [((Level, Index, String), BorderPtty)]
extractVars lvl tv =
  get'
    >>= \env -> case tv of
      FI name s e :?> TVVar _ lvl' idx
        | lvl == lvl' -> do
            let borders = env !!! lvl !!! idx
            bots <- mapM (extractVars lvl') ((FI "" s e :?>) . bot <$> borders)
            tops <- mapM (extractVars lvl') ((FI "" s e :?>) . top <$> borders)
            p <- normalizeBorder borders
            pure $ ((lvl, idx, name), p) : concat bots ++ concat tops
      _ :?> TVArrow args ret -> do
        args' <- mapM (extractVars lvl) args
        ret' <- extractVars lvl ret
        pure $ concat args' ++ ret'
      _ :?> TVTuple elems -> concat <$> mapM (extractVars lvl) elems
      _ :?> TVRecord fields ->
        concat
          <$> mapM (extractVars lvl . snd) fields
      _x -> pure []

-- Interface