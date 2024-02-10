{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
module Data.Vector.Storable.Mutable.CAS where

import Control.Monad
import Foreign.Storable
import Data.Vector.Storable.Mutable
import GHC.Exts
import GHC.Float
import GHC.ForeignPtr
import GHC.IO


-- | Returns whether the CAS succeeded, as well as the /old/ value in the array.
--
-- This function only works on platforms where 'Double#' and 'Word#' are the same size.
casIOVectorDouble :: IOVector Double -> Int -> Double -> Double -> IO (Bool, Double)
casIOVectorDouble (MVector _ (ForeignPtr addr _)) idx (D# check) (D# repl) = do
  let size = sizeOf (undefined :: Word)

  when (sizeOf (undefined :: Double) /= size) $
    error $ "casIOVectorDouble: Double is not word-sized (" ++
            show (sizeOf (undefined :: Double)) ++ " /= " ++ show size ++ ")"

  let checkword = word64ToWord# (stgDoubleToWord64 check)
      replword = word64ToWord# (stgDoubleToWord64 repl)
      !(I# byteoff) = idx * size
  IO $ \s -> case atomicCasWordAddr# (plusAddr# addr byteoff) checkword replword s of
               (# s', oldword #) ->
                 (# s', (W# oldword == W# checkword
                        ,D# (stgWord64ToDouble (wordToWord64# oldword))) #)
