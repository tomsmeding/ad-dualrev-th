{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
module Test.Parallel where

import Control.Concurrent
import Control.Monad ((>=>))


data Parallel a where
  Spawn :: IO a -> Parallel a
  Direct :: IO a -> Parallel a
  Ap :: Parallel (a -> b) -> Parallel a -> Parallel b
  Action :: Parallel a -> (a -> IO ()) -> Parallel a

instance Functor Parallel where
  fmap f (Spawn x) = Spawn (f <$> x)
  fmap f (Direct x) = Direct (f <$> x)
  fmap f (pf `Ap` px) = fmap (f .) pf `Ap` px
  fmap f a@Action{} = pure f `Ap` a

instance Applicative Parallel where
  pure = Direct . pure
  (<*>) = Ap

run :: IO () -> Parallel ()
run = Action (pure ()) . const

evalSpawns :: Parallel a -> IO (Parallel a)
evalSpawns = \case
  Spawn x -> do
    var <- newEmptyMVar
    _ <- forkIO $ x >>= putMVar var
    return (Direct (readMVar var))
  Direct x -> return (Direct x)
  Ap f x -> Ap <$> evalSpawns f <*> evalSpawns x
  Action p act -> Action <$> evalSpawns p <*> return act

evalSequential :: Parallel a -> IO a
evalSequential = \case
  Spawn act -> act
  Direct act -> act
  Ap f x -> ($) <$> evalSequential f <*> evalSequential x
  Action p act -> do
    x <- evalSequential p
    act x
    return x

evalSequentialNoSpawn :: Parallel a -> IO a
evalSequentialNoSpawn = \case
  Spawn{} -> error "Spawn detected in evalParallel"
  Direct act -> act
  Ap f x -> ($) <$> evalSequential f <*> evalSequential x
  Action p act -> do
    x <- evalSequential p
    act x
    return x

evalParallel :: Parallel a -> IO a
evalParallel = evalSpawns >=> evalSequentialNoSpawn
