{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE GADTSyntax #-}
module Data.Array.Growable (
  GrowArray,
  alloc,
  allocBeside,
  set,
  push,
  get,
  size
) where

import qualified Data.Array.Mutable.Linear as A
import GHC.Stack (HasCallStack)
import Prelude.Linear


todo = "TODO: automatically grow array on set, and return default on out-of-bounds get"


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
  | 0 <= i, i < len = GrowArray len def (A.set i x a)
  | otherwise = a `lseq` error ("Index out of bounds: " ++ show i)

push :: a -> GrowArray a %1-> GrowArray a
push x (GrowArray len def a) = case A.size a of
  (Ur cap, a') | cap < len -> GrowArray (succ len) def (A.set len x a')
               | otherwise -> push x (GrowArray len def (A.resize (2 * cap) def a'))

get :: Int -> GrowArray a %1-> (Ur a, GrowArray a)
get i (GrowArray len def a)
  | 0 <= i, i < len = case A.get i a of (x, a') -> (x, GrowArray len def a')
  | otherwise = a `lseq` error ("Index out of bounds: " ++ show i)

size :: GrowArray a %1-> (Ur Int, GrowArray a)
size (GrowArray len def a) = (Ur len, GrowArray len def a)
