{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE InstanceSigs #-}

module Typing where

import           Syn (Statement(..), TypeTerm(TLam), ExprTerm(Fun))
import           ElabUtils (ElabStage(..), ElabError, ElabEnv(ElabEnv))
import           EvalTUtils (EvalTStage(Unevaluated, Evaluated, EvaluationError)
                           , TypeVal, EvalTError, EvalTEnv(EvalTEnv))
import           Control.Monad.State (State, modify, gets, evalState)
import           GHC.Arr ((//), array, Array, (!))
import qualified ElabUtils as Elab
import qualified Elab
import           Utils (MState(runMState), success, fatal, info, tr, warn)
import           Elab (elaborate, indexType)
import           Data.Traversable (forM)
import qualified EvalT
import qualified EvalTUtils as EvalT
import           Debug.Trace (traceM)
import           Data.Maybe (fromJust)

data Context = Context { valBindings :: [(String, ElabStage)]
                       , tyBindings :: [(String, EvalTStage)]
                       , constraints :: Elab.ConstrEnv
                       , counter :: Int
                       }

data TypingError = ElabStageError ElabError
                 | EvalTStageError EvalTError

data TypingSuccess =
  TypingSuccess { prettyTypingSuccess :: String, rawTypingSuccess :: TypeVal }

instance Show TypingSuccess where
  show :: TypingSuccess -> String
  show (TypingSuccess x _) = x

newtype TypingResult = TypingResult [(String, Either TypingError TypingSuccess)]

instance Show TypingResult where
  show :: TypingResult -> String
  show (TypingResult res) = unlines
    $ map
      (\(name, res') -> info name
       ++ ": "
       ++ case res' of
         Left (ElabStageError err)    -> fatal $ "[Elab] " ++ show err
         Left (EvalTStageError err)   -> fatal $ "[Eval] " ++ show err
         Right (TypingSuccess ptty _) -> success ptty)
      res

type TypingState = State Context

succ :: TypingState Int
succ = do
  counter' <- gets counter
  modify $ \ctx -> ctx { counter = counter' + 1 }
  return counter'

addTypeBinding :: String -> TypeTerm -> TypingState ()
addTypeBinding name ty = modify
  $ \ctx -> ctx { tyBindings = (name, Unevaluated ty):tyBindings ctx }

addValBinding :: String -> ExprTerm -> TypingState ()
addValBinding name term = modify
  $ \ctx -> ctx { valBindings = (name, Unelaborated term):valBindings ctx }

putTypeBinding :: String -> EvalTStage -> TypingState ()
putTypeBinding name ty = do
  tyBindings' <- gets tyBindings
  let new_tbds = (name, ty):filter ((/= name) . fst) tyBindings'
  modify $ \ctx -> ctx { tyBindings = new_tbds }

putValBinding :: String -> ElabStage -> TypingState ()
putValBinding name term = do
  valBindings' <- gets valBindings
  let new_vbds = (name, term):filter ((/= name) . fst) valBindings'
  modify $ \ctx -> ctx { valBindings = new_vbds }

genElabEnv :: TypingState ElabEnv
genElabEnv = do
  tyBindings' <- gets tyBindings
  valBindings' <- gets valBindings
  counter' <- gets counter
  traceM $ "Counter: " ++ show counter'
  constrs <- gets constraints
  let typeBindings = do
        (name, Unevaluated ty) <- tyBindings'
        return (name, ty)
  return $ ElabEnv counter' valBindings' typeBindings constrs

genEvalTEnv :: ElabEnv -> TypingState EvalTEnv
genEvalTEnv Elab.ElabEnv { Elab.constrs = c, Elab.counter = count } = do
  traceM $ show c
  tyBindings' <- gets tyBindings
  let constr' = array (0, count - 1)
        $ do
          i' <- [0 .. count - 1]
          Elab.Constr tops bots _ <- fromJust <$> [c ! i']
          let x = EvalT.Constr' (Left tops) (Left bots)
          return (i', x)
  return
    $ EvalTEnv
      constr'
      (array (0, 1024) [(i', Nothing) | i' <- [0 .. 1024]])
      tyBindings'
      0
      []
      0
      False

initEnv :: [Statement] -> TypingState ()
initEnv = mapM_
  $ \case
    LetDecl name _ty term        -> addValBinding name term
    FunDecl name pat ty term     -> addValBinding name (Fun pat ty term)
    TypeDecl name Nothing ty     -> addTypeBinding name ty
    TypeDecl name (Just vars) ty -> do
      refs <- mapM (const Typing.succ) vars
      let indexed_ty = indexType Nothing (zip vars refs) ty
      addTypeBinding name $ TLam refs indexed_ty

elabProgram :: Int -> TypingState ()
elabProgram i = gets (length . valBindings)
  >>= \case
    x
      | x == i -> return ()
      | otherwise -> do
        elabEnv <- genElabEnv
        case Elab.bindings elabEnv !! i of
          (_, Elaborated _)         -> elabProgram (i + 1)
          (name, Unelaborated term) -> do
            case runMState (elaborate term) elabEnv of
              Left err -> putValBinding name (ElaborationError err)
              Right (Elab.ElabResult ty _, env) -> do
                let elabEnv' = Elab.bindings env
                let constrs = Elab.constrs env
                let counter' = Elab.counter env
                modify
                  $ \ctx -> ctx { valBindings = elabEnv'
                                , constraints = constrs
                                , counter = counter'
                                }
                putValBinding name (Elaborated ty)
                elabProgram (i + 1)
          (_, ElaborationError err) -> do
            putValBinding (show err) (ElaborationError err)
            elabProgram (i + 1)

evalTProgram :: ElabEnv -> Int -> TypingState ()
evalTProgram elabEnv i = gets (length . tyBindings)
  >>= \case
    x
      | x == i -> return ()
      | otherwise -> do
        evalTEnv <- genEvalTEnv elabEnv
        case EvalT.freeBindings evalTEnv !! i of
          (_, Evaluated _)         -> evalTProgram elabEnv (i + 1)
          (name, Unevaluated ty)   -> do
            case runMState (EvalT.evalT ty) evalTEnv of
              Left err         -> putTypeBinding name (EvaluationError err)
              Right (ty', env) -> do
                let evalTEnv' = EvalT.freeBindings env
                modify $ \ctx -> ctx { tyBindings = evalTEnv' }
                putTypeBinding name (Evaluated ty')
                evalTProgram elabEnv (i + 1)
          (_, EvaluationError err) -> do
            putTypeBinding (show err) (EvaluationError err)
            evalTProgram elabEnv (i + 1)

typeProgram :: [Statement] -> TypingState TypingResult
typeProgram stmts = do
  initEnv stmts
  elabProgram 0
  elabEnv <- genElabEnv
  evalTProgram elabEnv 0
  evalTEnv <- genEvalTEnv elabEnv
  result <- forM (Elab.bindings elabEnv)
    $ \case
      (name, Elaborated ty)        -> do
        case runMState
          (do
             evaled <- EvalT.evalT ty
             ptty <- EvalT.pretty evaled
             return (evaled, ptty))
          evalTEnv of
          Right
            ((ty', ptty), _) -> return (name, Right $ TypingSuccess ptty ty')
          Left err -> return (name, Left $ EvalTStageError err)
      (name, ElaborationError err) -> return (name, Left $ ElabStageError err)
      (_, Unelaborated _)          -> error "Impossible"
  return $ TypingResult result

runTyping :: [Statement] -> TypingResult
runTyping stmts =
  evalState (typeProgram stmts) (Context [] [] Elab.initialConstrEnv 0)