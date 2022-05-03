{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
module Main where

import Control.DeepSeq (NFData, deepseq)
import Criterion
import qualified Criterion.Main as Criterion

import DFunction
import Language.Haskell.TH.Stupid
import Test.Approx
import Test.Framework


newtype FMult s = MkFMult (s, s)
  deriving (Show, Functor, Foldable, Traversable)
  deriving (Approx, Arbitrary, NFData) via (s, s)
fmult :: DFunction FMult
fmult = $$(makeFunction (parseType "FMult Double")
  [|| \arg -> case arg of MkFMult (x, y) -> x * y ||])

newtype FDotProd s = FDotProd ([s], [s])
  deriving (Show, Functor, Foldable, Traversable)
  deriving (Approx, Arbitrary, NFData) via ([s], [s])
fdotprod :: DFunction FDotProd
fdotprod = $$(makeFunction (parseType "FDotProd Double")
  [|| \(FDotProd (l1, l2)) ->
        let zipWith' f (x:xs) (y:ys) = f x y : zipWith' f xs ys
            zipWith' _ _ _ = []
            sum' [] = 0.0
            sum' (x:xs) = x + sum' xs
        in sum' (zipWith' (\x y -> x * y) l1 l2) ||])

newtype FSumMatVec s = FSumMatVec ([[s]], [s])
  deriving (Show, Functor, Foldable, Traversable)
  deriving (Approx, Arbitrary, NFData) via ([[s]], [s])
fsummatvec :: DFunction FSumMatVec
fsummatvec = $$(makeFunction (parseType "FSumMatVec Double")
  [|| \(FSumMatVec (m, v)) ->
        let zipWith' f (x:xs) (y:ys) = f x y : zipWith' f xs ys
            zipWith' _ _ _ = []
            sum' [] = 0.0
            sum' (x:xs) = x + sum' xs
            dotp v1 v2 = sum' (zipWith' (\x y -> x * y) v1 v2)
            map' _ [] = []
            map' f (x:xs) = f x : map' f xs
        in sum' (map' (dotp v) m) ||])

main :: IO ()
main = do
  -- runTestsExit $
  --   tree "correctness"
  --     [changeArgs (\args -> args { maxSuccess = 50000 }) $
  --      tree "fast"
  --        [property "fmult" (\x -> radWithTH fmult x ~= radWithAD fmult x)
  --        ,property "fdotprod" (\x -> radWithTH fdotprod x ~= radWithAD fdotprod x)]
  --     ,changeArgs (\args -> args { maxSuccess = 5000 }) $
  --      tree "slow"
  --        [property "fsummatvec" (\x -> radWithTH fsummatvec x ~= radWithAD fsummatvec x)]]

  Criterion.defaultMain
    [bgroup "fmult"
      [bench "TH" (nf (radWithTH fmult) (MkFMult (3.0, 4.0)))
      ,bench "ad" (nf (radWithAD fmult) (MkFMult (3.0, 4.0)))]
    ,bgroup "fdotprod"
      [bench "TH" (toBenchmarkable $ \n ->
                     let l1 = take (fromIntegral n) [1..]
                         l2 = take (fromIntegral n) [3,5..]
                     in radWithTH fdotprod (FDotProd (l1, l2)) `deepseq` return ())
      ,bench "ad" (toBenchmarkable $ \n ->
                     let l1 = take (fromIntegral n) [1..]
                         l2 = take (fromIntegral n) [3,5..]
                     in radWithAD fdotprod (FDotProd (l1, l2)) `deepseq` return ())]
    ,bgroup "fsummatvec"
      [bench "TH" (toBenchmarkable $ \n ->
                     let l1 = take (fromIntegral n) (blockN (fromIntegral n) [1..])
                         l2 = take (fromIntegral n) [3,5..]
                     in radWithTH fsummatvec (FSumMatVec (l1, l2)) `deepseq` return ())
      ,bench "ad" (toBenchmarkable $ \n ->
                     let l1 = take (fromIntegral n) (blockN (fromIntegral n) [1..])
                         l2 = take (fromIntegral n) [3,5..]
                     in radWithAD fsummatvec (FSumMatVec (l1, l2)) `deepseq` return ())]
    ]
  where
    blockN :: Int -> [a] -> [[a]]
    blockN _ [] = []
    blockN n l = let (pre, post) = splitAt n l in pre : blockN n post
