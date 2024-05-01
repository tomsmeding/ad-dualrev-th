{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE BangPatterns #-}
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
  forkJoin,

  -- * Debug
  debug,
) where

import Control.Concurrent
import Control.DeepSeq
import Control.Exception
import Control.Monad
import Data.IORef
import qualified Data.Vector as V
import System.Clock
import System.IO
import System.IO.Unsafe
import Numeric


foreign import ccall "setup_rts_gc_took_tom" c_setup_rts_gc_took_tom :: IO ()


ts2float :: TimeSpec -> Double
ts2float t = fromIntegral (toNanoSecs (diffTimeSpec epoch t)) / 1e6 :: Double

tsdiff2float :: TimeSpec -> Double
tsdiff2float t = fromIntegral (toNanoSecs t) / 1e6 :: Double


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
  t1 <- getTime Monotonic
  _ <- evaluate (force s)
  t2 <- getTime Monotonic
  me <- myThreadId
  withMVar debugLock $ \() ->
    hPutStrLn stderr $ "@" ++ showFFloat (Just 4) (ts2float t1) " @" ++ showFFloat (Just 4) (ts2float t2) "" ++ " [" ++ show me ++ "] " ++ s


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
globalThreadPool = unsafePerformIO $ do
  when kENABLE_DEBUG c_setup_rts_gc_took_tom
  mkPool

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
      debug $ "waiting"
      -- When the pool is dropped, the channels are also dropped, and this
      -- readChan will block indefinitely, raising the exception, which makes
      -- the worker exit and all is good.
      mjob <- catch (Just <$> readChan chan) $ \(_ :: BlockedIndefinitelyOnMVar) -> return Nothing
      forM_ @Maybe mjob $ \ job@(Job jobid _) -> do
        debug $ "[" ++ show jobid ++ "] << popped job"
        runJobHere job
        loop

runJobHere :: Job -> IO ()
runJobHere (Job jobid ref) = do
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
      debug $ "[" ++ show jobid ++ "] job took " ++ show (tsdiff2float (diffTimeSpec t1 t2)) ++ " ms"
      _ <- forkIO $ do
        me <- myThreadId
        debug $ "[" ++ show jobid ++ "] running cont -> " ++ show me
        cont res
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
  ref <- newIORef (Just (JobPayload work cont))
  writeChan chan (Job jobid ref)
  return (JobRef jobid ref)

-- | If the job has not started executing on a worker thread yet, run it here
-- in this thread. The claiming of the job is atomic, so the job will be run
-- only once in total. Furthermore this function is idempotent: running it
-- multiple times simply does nothing when the job was already stolen.
tryStealJob :: JobRef a -> IO ()
tryStealJob (JobRef jobid ref) = do
  debug $ "[" ++ show jobid ++ "] trying to steal job:"
  runJobHere (Job jobid ref)

forkJoin :: Pool -> IO a -> IO b -> (a -> b -> IO ()) -> IO ()
forkJoin pool m1 m2 mk = do
  cell1 <- newEmptyMVar
  cell2 <- newEmptyMVar
  contcell <- newMVar mk

  let finish mycell othercell f x = do
        putMVar mycell x
        tryReadMVar othercell >>= \case
          Nothing -> return ()  -- other is not yet done, other will see our value
          Just y -> tryTakeMVar contcell >>= \case
            Nothing -> return ()  -- we saw each others' values, other was first
            Just cont -> f cont x y

  _ <- submitJob pool m1 (finish cell1 cell2 id)
  _ <- submitJob pool m2 (finish cell2 cell1 flip)
  return ()
