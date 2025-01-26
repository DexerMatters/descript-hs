{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}

module EvalT where

import           Syn (TypeTerm(..))
import           EvalTUtils hiding (bots, ident)
import           Utils (throw, all', put, save, get, gets, modify)
import           Control.Monad
import           Data.List (intercalate)
import           GHC.Base (Alternative((<|>)))

evalT :: TypeTerm -> EvalTState TypeVal
evalT (TVar n) = lookupBinding' n
evalT (TFree s) = do
  tbds <- gets freeBindings
  case lookup s tbds of
    Just (Evaluated ty) -> pure ty
    Just (Unevaluated ty) -> do
      eval <- evalT ty
      let new_bds = map
            (\(s', ty') -> if s == s'
                           then (s', Evaluated eval)
                           else (s', ty'))
            tbds
      modify $ \env -> env { freeBindings = new_bds }
      pure eval
    Just (EvaluationError err) -> throw err
    Nothing -> throw $ UnboundTypeIdent s
evalT (TFix n) = get >>= \env -> pure $ TVFix (TLazy env (TVar n))
evalT (TPrimitive p) = pure $ TVPrimitive p
evalT (TArrow args ret) = TVArrow <$> mapM evalT args <*> evalT ret
evalT (TTuple ts) = TVTuple <$> mapM evalT ts
evalT (TRecord fields) = TVRecord
  <$> mapM (\(name, ty) -> (name, ) <$> evalT ty) fields
evalT (TLam refs ty) = TVLam <$> (TClosure refs <$> get <*> pure ty)
evalT (TApp lam [] inputs) = do
  modify $ \env -> env { fixFlag = True }
  let reduce = \case
        TVLam (TClosure refs env body) -> do
          -- Eval input types
          input_types <- mapM evalT inputs
          unless (length refs == length input_types)
            $ throw
            $ InadequateTypeArity
              (TVLam (TClosure refs env body))
              (TVTuple input_types)
          save
            $ do
              put env
              forM_ refs (\ref -> newBinding ref (TVVar ref))
              zipWithM_
                (\arg_type input_type -> arg_type <: input_type
                 >>= \case
                   Just True -> pure ()
                   _         -> throw $ BadConversion arg_type input_type)
                (map TVVar refs)
                input_types
          -- Eval body
          save
            $ put env >> zipWithM_ newBinding refs input_types >> evalT body
            >>= exact
        TVVar x -> exact (TVVar x) >>= reduce
        TVFix (TLazy _ term) -> get
          >>= \env -> pure $ TVFix $ TLazy env (TApp term [] inputs)
        _ -> error "Impossible"
  result <- evalT lam >>= reduce
  modify $ \env -> env { fixFlag = False }
  pure result
evalT (TApp lam args inputs) = evalT lam
  >>= \case
    TVLam (TClosure refs env body) -> do
      -- Eval input types
      input_types <- mapM evalT inputs
      -- Eval argument types
      arg_types <- save
        $ do
          put env
          forM_ refs (\ref -> newBinding ref (TVVar ref))
          arg_types <- mapM evalT args
          zipWithM_
            (\arg_type input_type -> input_type <: arg_type
             >>= \case
               Just True -> pure ()
               _         -> throw $ BadConversion arg_type input_type)
            arg_types
            input_types
          pure arg_types
      -- Eval body
      save
        $ put env
        >> zipWithM_ (deduce refs) input_types arg_types
        >> evalT body
        >>= exact
    _ -> error "Impossible"
evalT (TConv from to) = do
  from_type <- evalT from
  to_type <- evalT to
  from_type <: to_type
    >>= \case
      Just True -> pure to_type
      _         -> throw $ BadConversion from_type to_type
evalT (TSeq seq) = do
  types <- mapM evalT seq
  pure $ last types
evalT (TLet ref ty body) = save
  $ do
    ty' <- evalT ty
    newBinding ref ty'
    evalT body
evalT THole = throw UnexpectedHole

($$) :: TClosure -> [TypeVal] -> EvalTState TypeVal
TClosure refs env ty $$ args = save
  $ put env >> mapM_ (uncurry newBinding) (zip refs args) >> evalT ty

-- | Convert a type term to a type value
--  Conversion is valid only if rhs is more general than lhs
(<:) :: TypeVal -> TypeVal -> EvalTState (Maybe Bool)
TVPrimitive p <: TVPrimitive p' = pure $ Just $ p == p'
TVArrow args ret <: TVArrow args' ret' = do
  -- Contravariance for arguments
  arg_res <- zipWithM (<:) args' args
  -- Covariance for return type
  ret_res <- ret <: ret'
  pure $ all' (ret_res:arg_res)
TVTuple ts <: TVTuple ts' = do
  res <- zipWithM (<:) ts ts'
  pure $ all' res
-- field' has to be a subset of field
TVRecord fields <: TVRecord fields' = do
  res <- forM fields'
    $ \(x, ty') -> case lookup x fields of
      Just ty -> ty <: ty'
      Nothing -> pure Nothing
  pure $ all' res
TVVar ref <: rhs = do
  -- bots are more general limit
  -- tops are more specific limit
  -- rhs is more general than the TVVar, which means 
  -- rhs has to be more general than the bots

  bots <- getBots evalT ref
  bot_res <- mapM (rhs <:) bots
  pure $ all' bot_res
lhs <: TVVar ref = do
  -- lhs is more specific than the TVVar, which means
  -- lhs has to be more specific than the tops
  tops <- getTops evalT ref
  top_res <- mapM (<: lhs) tops
  pure $ all' top_res
TVLam cls@(TClosure ref _ _) <: ty = do
  -- Eval the exact type of the abstraction
  let args = map TVVar ref
  rhs <- cls $$ args
  rhs <: ty
ty <: TVLam cls@(TClosure ref _ _) = do
  -- Eval the exact type of the abstraction
  let args = map TVVar ref
  rhs <- cls $$ args
  ty <: rhs
_ <: _ = pure Nothing

deduce :: [Int]    -- ^ References
       -> TypeVal  -- ^ Input type
       -> TypeVal  -- ^ Argument type
       -> EvalTState ()
deduce [] a b = throw $ InadequateTypeArity a b
deduce refs (TVLam cls@(TClosure refs' _ _)) ty = do
  let args = map TVVar refs'
  ret <- cls $$ args
  deduce (refs ++ refs') ret ty
deduce refs ty (TVLam cls@(TClosure refs' _ _)) = do
  let args = map TVVar refs'
  ret <- cls $$ args
  deduce (refs ++ refs') ty ret
deduce refs input_type (TVVar ref) = do
  when (ref `elem` refs) $ newBinding ref input_type
  getTops evalT ref >>= mapM_ (deduce refs input_type)
  getBots evalT ref >>= mapM_ (deduce refs input_type)
deduce refs (TVTuple ts) (TVTuple ts') = do
  zipWithM_ (deduce refs) ts ts'
deduce refs a@(TVRecord fields) b@(TVRecord fields') = do
  forM_ fields'
    $ \(name, ty') -> case lookup name fields of
      Just ty -> deduce refs ty ty'
      Nothing -> throw $ InadequateTypeArity a b
deduce refs (TVArrow args ret) (TVArrow args' ret') = do
  zipWithM_ (deduce refs) args' args
  deduce refs ret ret'
deduce _ _ _ = pure ()

exact :: TypeVal -> EvalTState TypeVal
exact (TVVar ref) = (lookupBinding ref >>= exact) <|> pure (TVVar ref)
exact (TVTuple ts) = TVTuple <$> mapM exact ts
exact (TVRecord fields) = TVRecord
  <$> mapM (\(name, ty) -> (name, ) <$> exact ty) fields
exact (TVArrow args ret) = TVArrow <$> mapM exact args <*> exact ret
exact (TVFix fix) = pure $ TVFix fix
exact ty = pure ty

pretty :: TypeVal -> EvalTState String
pretty (TVPrimitive p) = pure $ show p
pretty (TVVar ref) = lookupFresh ref
pretty (TVFix _) = pure "..."
pretty (TVTuple ts) = do
  ts' <- mapM pretty ts
  pure $ "(" ++ intercalate ", " ts' ++ ")"
pretty (TVRecord fields) = do
  fields' <- mapM (\(name, ty) -> ((name ++ ": ") ++) <$> pretty ty) fields
  pure $ "{ " ++ intercalate ", " fields' ++ " }"
pretty (TVArrow args ret) = do
  args' <- mapM pretty args
  ret' <- pretty ret
  pure $ "(" ++ intercalate ", " args' ++ ") -> " ++ ret'
pretty (TVLam cls@(TClosure refs _ _)) = do
  let args = map TVVar refs
  args' <- mapM pretty args
  ret <- cls $$ args
  ret' <- block $ pretty ret
  pure $ "forall<" ++ intercalate ", " args' ++ ">. " ++ ret'

strict :: TLazy -> EvalTState TypeVal
strict (TLazy env term) = save
  $ do
    put env
    evalT term