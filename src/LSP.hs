{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module LSP where

import Control.Exception (throwIO)
import Control.Monad (forM, forM_)
import Control.Monad.Identity (Identity (runIdentity))
import Data.Bitraversable (bimapM)
import Data.Data (Data, Typeable)
import Data.Either (fromRight, lefts, rights)
import Data.IORef (IORef, modifyIORef', newIORef)
import Data.List (nub, sortOn)
import Data.List.NonEmpty (toList)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Ord (Down (Down))
import qualified Data.Set as Set
import GHC.IORef (readIORef)
import GHC.TopHandler (runIO)
import Parser (allowedAll)
import Pretty (render)
import Syn (ExprTerm')
import System.Exit (exitSuccess)
import Text.JSON.Generic (encodeJSON)
import Text.Megaparsec (parse)
import Text.Megaparsec.Error
import TypeElab (elaborate, quoteError, quoteType)
import TypePretty
import TypeUtils hiding (traces)
import Utils hiding (end, start)

data HoverMessage = HoverMessage
  { content :: String,
    range :: Range
  }
  deriving (Show, Data, Typeable)

data Diagnostic = Diagnostic
  { range :: Range,
    message :: String,
    severity :: Int
  }
  deriving (Show, Data, Typeable)

data CompletionMessage = CompletionMessage
  { completions :: [CompletionItem],
    range :: Range
  }
  deriving (Show, Data, Typeable)

data CompletionItem = CompletionItem
  { label :: String,
    kind :: Int,
    index :: Int, -- data
    detail :: String,
    documentation :: String
  }
  deriving (Show, Data, Typeable)

generateMessages :: String -> IO ()
generateMessages code = runIO $ do
  diags <- newIORef []
  hovers <- newIORef []
  comps <- newIORef []

  term <- case generateDiagnosticFromParser code of
    Left diags' -> do
      modifyIORef' diags (diags' ++)
      output diags hovers comps
    Right term -> return term

  let env@(TypeEnv _ traces scopes) =
        runIdentity $
          execTypeChecker (elaborate [] term)

  let traces' =
        fromRight (error "Never happen") $
          runIdentity $
            runTypeChecker' env (mapM (bimapM quoteError quoteType) traces)

  let scopeTraces =
        fromRight (error "Never happen") $
          runIdentity $
            runTypeChecker' env (mapM (secondM (mapM (secondM quoteType))) scopes)

  let hoverTraces = sortOn (Down . fi) (rights traces')
  let diagTraces = nub $ lefts traces'

  forM_ diagTraces $ \case
    (FI _ s e :?> errMsg) ->
      modifyIORef' diags (Diagnostic (Range s e) (render errMsg) 1 :)
    _ -> throwIO $ userError "This should never happen"
  forM_ hoverTraces $ \case
    tv@(FI _ s e :?> _) ->
      modifyIORef' hovers (HoverMessage (render $ pretty0 tv) (Range s e) :)
    _ -> throwIO $ userError "This should never happen"

  counter <- newIORef (-1)

  forM_ scopeTraces $ \(r, bindings) -> do
    messages <- forM bindings $ \(name, tv) -> do
      modifyIORef' counter (+ 1)
      i <- readIORef counter
      pure
        CompletionItem
          { label = name,
            kind = 1,
            index = i,
            detail = render $ pretty0 tv,
            documentation = ""
          }
    modifyIORef' comps (CompletionMessage messages r :)

  output diags hovers comps
  where
    secondM f (a, b) = (a,) <$> f b

generateDiagnosticFromParser :: String -> Either [Diagnostic] ExprTerm'
generateDiagnosticFromParser code =
  case parse allowedAll "" code of
    Left err ->
      let diags' = flip NonEmpty.map (bundleErrors err) $
            \case
              TrivialError offset unexp exps ->
                let range = case unexp of
                      Just x -> case x of
                        Label s -> Range offset (offset + length s)
                        Tokens ts -> Range offset (offset + length ts)
                        EndOfInput -> Range offset (length code)
                      Nothing -> Range offset (length code)
                    unexpected = case unexp of
                      Just x -> case x of
                        Label s -> "Unexpected " ++ toList s
                        Tokens ts -> "Unexpected " ++ toList ts
                        EndOfInput -> "Unexpected end of input"
                      Nothing -> "Unexpected end of input"
                    expected = case Set.toList exps of
                      [] -> ""
                      x -> (++) "\nExpected " $
                        flip concatMap x $
                          \case
                            Label s -> toList s ++ " "
                            Tokens ts -> toList ts ++ " "
                            EndOfInput -> "end of input "
                 in Diagnostic
                      { range,
                        severity = 1,
                        message = unexpected ++ expected
                      }
              FancyError _ _ ->
                Diagnostic
                  { range = Range 0 0,
                    message = "Fancy error",
                    severity = 1
                  }
       in Left (toList diags')
    Right x -> Right x

output :: IORef [Diagnostic] -> IORef [HoverMessage] -> IORef [CompletionMessage] -> IO a
output diags hovers comps = do
  diags' <- encodeJSON <$> readIORef diags
  hovers' <- encodeJSON <$> readIORef hovers
  comps' <- encodeJSON <$> readIORef comps
  putStrLn $
    "{ \"diagnostics\": "
      ++ diags'
      ++ ", \"hovers\": "
      ++ hovers'
      ++ ", \"completions\": "
      ++ comps'
      ++ " }"
  exitSuccess