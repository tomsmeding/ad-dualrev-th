{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
module Control.Concurrent.ThreadPool (
  -- * Pools
  Pool,
  mkPool,
  mkPoolN,
  globalThreadPool,

  -- * Running jobs
  submitJob,
  JobRef,
  tryStealJob,

  -- * Debug
  debug,
) where

import Control.Concurrent
import Control.Exception
import Control.Monad
import Data.IORef
import qualified Data.Vector as V
import System.Clock
import System.IO
import System.IO.Unsafe
import Numeric


kENABLE_DEBUG :: Bool
kENABLE_DEBUG = True

{-# NOINLINE epoch #-}
epoch :: TimeSpec
epoch = unsafePerformIO $ getTime Monotonic

{-# NOINLINE debugLock #-}
debugLock :: MVar ()
debugLock = unsafePerformIO $ newMVar ()

debug :: String -> IO ()
debug _ | not kENABLE_DEBUG = return ()
debug s = do
  me <- myThreadId
  t <- getTime Monotonic
  withMVar debugLock $ \() ->
    hPutStrLn stderr $ "@" ++ showFFloat (Just 4) (fromIntegral (toNanoSecs (diffTimeSpec epoch t)) / 1e6 :: Double) "" ++ " [" ++ show me ++ "] " ++ s


-- | A thread pool.
data Pool = Pool (Chan Job) (V.Vector Worker) (IORef Int)

-- I don't think the ThreadId is actually used.
newtype Worker = Worker ThreadId

data Job = forall a. Job !Int !(IORef (Maybe (JobPayload a)))

data JobPayload a = JobPayload
  (IO a)        -- the work that will be done on the worker thread
  (a -> IO ())  -- consumer of the result, spawned in a simple forkIO (should be very cheap)

{-# NOINLINE globalThreadPool #-}
-- | A statically allocated thread pool.
globalThreadPool :: Pool
globalThreadPool = unsafePerformIO mkPool

-- | Create a new thread pool with one worker for every capability (see
-- 'getNumCapabilities').
mkPool :: IO Pool
mkPool = getNumCapabilities >>= mkPoolN

-- | Create a new thread pool with the given number of worker threads.
mkPoolN :: Int -> IO Pool
mkPoolN n = do
  chan <- newChan
  workers <- forM [0 .. n-1] (startWorker chan)
  jidref <- newIORef 0
  return (Pool chan (V.fromListN n workers) jidref)

startWorker :: Chan Job -> Int -> IO Worker
startWorker chan i = Worker <$> forkOn i loop
  where
    loop = do
      -- When the pool is dropped, the channels are also dropped, and this
      -- readChan will block indefinitely, raising the exception, which makes
      -- the worker exit and all is good.
      mjob <- catch (Just <$> readChan chan) $ \(_ :: BlockedIndefinitelyOnMVar) -> return Nothing
      forM_ @Maybe mjob $ \job@(Job jobid _) -> do
        debug $ "[" ++ show jobid ++ "] << popped job"
        runJobHere job
        loop

runJobHere :: Job -> IO ()
runJobHere (Job jobid ref) = do
  debug $ "[" ++ show jobid ++ "] going to claim"
  mpair <- atomicModifyIORef' ref (\case Nothing -> (Nothing, Nothing)
                                         Just x  -> (Nothing, Just x))
  case mpair of
    Nothing -> do
      debug $ "[" ++ show jobid ++ "] (got stolen job)"
    Just (JobPayload work cont) -> do  -- only do work if it hasn't been stolen yet
      t1 <- getTime Monotonic
      debug $ "[" ++ show jobid ++ "] accepted"
      res <- work
      t2 <- getTime Monotonic
      debug $ "[" ++ show jobid ++ "] job took " ++ show (fromIntegral (toNanoSecs (diffTimeSpec t1 t2)) / 1e6 :: Double) ++ " ms"
      _ <- forkIO (cont res)
      return ()

-- | A reference to a job so that it can be stolen.
data JobRef a = JobRef !Int (IORef (Maybe (JobPayload a)))

-- | Submit a job to a thread pool. The second argument (@work@) is the work to
-- be done on the worker thread; the third argument (@cont@) is a handler for
-- the result that runs /outside/ of the worker thread. This can make it easier
-- to prevent deadlocks due to submitting jobs from within a worker job.
submitJob :: Pool -> IO a -> (a -> IO ()) -> IO (JobRef a)
submitJob (Pool chan _ jidref) work cont = do
  jobid <- atomicModifyIORef' jidref (\i -> (i + 1, i))
  debug $ "[" ++ show jobid ++ "] >> submitJob"
  _ <- return $! jobid
  debug $ "[" ++ show jobid ++ "] >> submitJob eval"
  ref <- newIORef (Just (JobPayload work cont))
  writeChan chan $! Job jobid ref
  return (JobRef jobid ref)

-- | If the job has not started executing on a worker thread yet, run it here
-- in this thread. The claiming of the job is atomic, so the job will be run
-- only once in total. Furthermore this function is idempotent: running it
-- multiple times simply does nothing when the job was already stolen.
tryStealJob :: JobRef a -> IO ()
tryStealJob (JobRef jobid ref) = do
  debug $ "[" ++ show jobid ++ "] trying to steal job:"
  runJobHere (Job jobid ref)
