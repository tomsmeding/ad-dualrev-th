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
  scalePool,

  -- * Running jobs
  submitJob,

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
kENABLE_DEBUG = False

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
data Pool = Pool (Chan Job) (MVar (V.Vector Worker)) (IORef Int)

newtype Worker = Worker ThreadId

data Job = Job !Int !(IO ())

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
  listref <- newMVar (V.fromListN n workers)
  jidref <- newIORef 0
  return (Pool chan listref jidref)

startWorker :: Chan Job -> Int -> IO Worker
startWorker chan i = Worker <$> forkOn i loop
  where
    loop = do
      debug "waiting"
      -- When the pool is dropped, the channels are also dropped, and this
      -- readChan will block indefinitely, raising the exception, which makes
      -- the worker exit and all is good.
      mjob <- catch (Just <$> readChan chan) $ \(_ :: BlockedIndefinitelyOnMVar) -> return Nothing
      forM_ @Maybe mjob $ \(Job jobid work) -> do
        debug $ "[" ++ show jobid ++ "] << popped job"
        t1 <- getTime Monotonic
        work
        t2 <- getTime Monotonic
        debug $ "[" ++ show jobid ++ "] job took " ++ show (tsdiff2float (diffTimeSpec t1 t2)) ++ " ms"
        loop

-- | When the target size is smaller than the original size, this mercilessly
-- and immediately kills some workers. If you have jobs running, they may well
-- be cancelled.
scalePool :: Pool -> Int -> IO ()
scalePool (Pool chan listref _) target =
  modifyMVar listref $ \workers -> do
    -- either tokill == [] or news == []
    let (remain, tokill) = splitAt target (V.toList workers)
    forM_ tokill $ \(Worker tid) -> killThread tid
    news <- forM [V.length workers .. target - 1] $ \i -> startWorker chan i
    return (V.fromList (remain ++ news), ())

-- | Submit a job to a thread pool.
submitJob :: Pool -> IO () -> IO ()
submitJob (Pool chan _ jidref) work = do
  jobid <- atomicModifyIORef' jidref (\i -> (i + 1, i))
  debug $ "[" ++ show jobid ++ "] >> submitJob"
  writeChan chan (Job jobid work)
