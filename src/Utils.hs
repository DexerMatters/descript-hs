{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TupleSections #-}

module Utils where

import           Control.Applicative (Alternative(empty, (<|>)))
import           Debug.Trace
import           GHC.Base (liftA2)

newtype MState s e a = MState { runMState :: s -> Either e (a, s) }

instance Functor (MState s e) where
  fmap :: (a -> b) -> MState s e a -> MState s e b
  fmap f (MState g) = MState
    $ \s -> case g s of
      Left e        -> Left e
      Right (a, s') -> Right (f a, s')

instance Applicative (MState s e) where
  pure :: a -> MState s e a
  pure a = MState $ \s -> Right (a, s)

  (<*>) :: MState s e (a -> b) -> MState s e a -> MState s e b
  MState f <*> MState g = MState
    $ \s -> case f s of
      Left e        -> Left e
      Right (h, s') -> case g s' of
        Left e'        -> Left e'
        Right (a, s'') -> Right (h a, s'')

instance Monad (MState s e) where
  return :: a -> MState s e a
  return = pure

  (>>=) :: MState s e a -> (a -> MState s e b) -> MState s e b
  MState f >>= g = MState
    $ \s -> case f s of
      Left e        -> Left e
      Right (a, s') -> let MState h = g a
                       in h s'

instance Alternative (MState s e) where
  empty :: MState s e a
  empty = MState $ \_ -> Left undefined

  (<|>) :: MState s e a -> MState s e a -> MState s e a
  MState f <|> MState g = MState
    $ \s -> case f s of
      Left _ -> g s
      x      -> x

get :: MState s e s
get = MState $ \s -> Right (s, s)

gets :: (s -> a) -> MState s e a
gets f = f <$> get

put :: s -> MState s e ()
put s = MState $ \_ -> Right ((), s)

modify :: (s -> s) -> MState s e ()
modify f = MState $ \s -> Right ((), f s)

throw :: e -> MState s e a
throw e = MState $ \_ -> Left e

catch :: MState s e a -> (e -> MState s e a) -> MState s e a
catch (MState f) g = MState
  $ \s -> case f s of
    Left e        -> let MState h = g e
                     in h s
    Right (a, s') -> Right (a, s')

save :: MState s e a -> MState s e a
save f = do
  s <- get
  a <- f
  put s
  pure a

-- | Implementation for debugging purposes

tr :: Show a => a -> a
tr x = trace ("[TRACE] " ++ show x) x

-- | Ternary boolearn operator

(&&&) :: Maybe Bool -> Maybe Bool -> Maybe Bool
(&&&) = liftA2 (&&)

(|||) :: Maybe Bool -> Maybe Bool -> Maybe Bool
(|||) = liftA2 (||)

all' :: [Maybe Bool] -> Maybe Bool
all' = foldr (&&&) (Just True)

any' :: [Maybe Bool] -> Maybe Bool
any' = foldr (|||) (Just False)

thd :: (a, b, c) -> c
thd (_, _, c) = c