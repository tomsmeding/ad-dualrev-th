{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE LambdaCase #-}
module Control.Concurrent.ForkJoin (
  Graph(..),
  execute,
) where

import Control.Concurrent.MVar
import Control.Concurrent.ThreadPool


data Graph a
  = forall b c. Fork (IO (Graph b)) (IO (Graph c)) (b -> c -> IO (Graph a))
  | Done a

execute :: IO (Graph a) -> IO a
execute graph =
  graph >>= \case
    node@Fork{} -> do
      pool <- mkPool
      executeIn pool node
    Done x -> return x

-- Invariant: this function does NOT run inside a job in the pool.
executeIn :: Pool -> Graph a -> IO a
executeIn pool (Fork m1 m2 cont) = do
  var1 <- newEmptyMVar
  var2 <- newEmptyMVar
  submitJob pool m1 $ \graph' -> executeIn pool graph' >>= putMVar var1
  submitJob pool m2 $ \graph' -> executeIn pool graph' >>= putMVar var2
  x1 <- readMVar var1
  x2 <- readMVar var2
  cont x1 x2 >>= executeIn pool
executeIn _ (Done x) = return x
