{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Control.Concurrent.ThreadPool (
  Pool,
  mkPool,
  mkPoolN,
  globalThreadPool,
  submitJob,
) where

import Control.Concurrent
import Control.Exception
import Control.Monad
import qualified Data.Vector as V
import System.IO.Unsafe


data Pool = Pool (Chan Job) (V.Vector Worker)

newtype Worker = Worker ThreadId

data Job =
  forall a. Job (IO a)  -- the work that will be done on the worker thread
                (a -> IO ())  -- consumer of the result, spawned in a simple forkIO (should be very cheap)

{-# NOINLINE globalThreadPool #-}
globalThreadPool :: Pool
globalThreadPool = unsafePerformIO mkPool

mkPool :: IO Pool
mkPool = getNumCapabilities >>= mkPoolN

mkPoolN :: Int -> IO Pool
mkPoolN n = do
  chan <- newChan
  Pool chan . V.fromListN n <$> forM [0 .. n-1] (startWorker chan)

startWorker :: Chan Job -> Int -> IO Worker
startWorker chan i = Worker <$> forkOn i loop
  where
    loop = do
      -- When the pool is dropped, the channels are also dropped, and this
      -- readChan will block indefinitely, raising the exception, which makes
      -- the worker exit and all is good.
      mjob <- catch (Just <$> readChan chan) $ \(_ :: BlockedIndefinitelyOnMVar) -> return Nothing
      case mjob of
        Just (Job work cont) -> do
          res <- work
          _ <- forkIO (cont res)
          loop
        Nothing -> return ()

submitJob :: Pool -> IO a -> (a -> IO ()) -> IO ()
submitJob (Pool chan _) work cont = writeChan chan (Job work cont)
