{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE GADTSyntax #-}
module Data.Array.Growable (
  GrowArray,
  alloc,
  allocBeside,
  set,
  get,
  size,
  freeze,
) where

import qualified Data.Array.Mutable.Linear as A
import qualified Data.Vector as V
import GHC.Stack (HasCallStack)
import Prelude.Linear


data GrowArray a where
  GrowArray :: Int -> a -> A.Array a %1-> GrowArray a

instance Consumable (GrowArray a) where
  consume (GrowArray _ _ a) = consume a

alloc :: HasCallStack => Int -> a -> (GrowArray a %1-> Ur b) %1-> Ur b
alloc n def f = A.alloc n def (f . GrowArray n def)

allocBeside :: Int -> a -> GrowArray b %1-> (GrowArray a, GrowArray b)
allocBeside n def (GrowArray otherlen otherdef other) =
  case A.allocBeside n def other of
    (arr, other') -> (GrowArray n def arr, GrowArray otherlen otherdef other')

set :: HasCallStack => Int -> a -> GrowArray a %1-> GrowArray a
set i x (GrowArray len def a)
  | i < 0 = a `lseq` error ("GrowArray.set: Negative index: " ++ show i)
  | i < len = GrowArray len def (A.set i x a)
  | otherwise = set i x (GrowArray (i + 1) def (A.resize (i + 1) def a))

get :: Int -> GrowArray a %1-> (Ur a, GrowArray a)
get i (GrowArray len def a)
  | i < 0 = a `lseq` error ("GrowArray.get: Negative index: " ++ show i)
  | i < len = case A.get i a of (x, a') -> (x, GrowArray len def a')
  | otherwise = (Ur def, GrowArray len def a)

size :: GrowArray a %1-> (Ur Int, GrowArray a)
size (GrowArray len def a) = (Ur len, GrowArray len def a)

freeze :: GrowArray a %1-> Ur (V.Vector a)
freeze (GrowArray len _ a) =
  case A.freeze a of Ur v -> Ur (V.slice 0 len v)
