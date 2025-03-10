{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
module Types where

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import Test.QuickCheck (Arbitrary(..))

import Test.Approx


data Vec3 s = Vec3 s s s
  deriving (Show, Functor, Foldable, Traversable, Generic)
instance NFData s => NFData (Vec3 s)
instance Arbitrary s => Arbitrary (Vec3 s) where arbitrary = Vec3 <$> arbitrary <*> arbitrary <*> arbitrary
instance Approx s => Approx (Vec3 s) where
  approx absdelta reldelta (Vec3 a b c) (Vec3 a' b' c') = approx absdelta reldelta [a,b,c] [a',b',c']

data Quaternion s = Quaternion s s s s
  deriving (Show, Functor, Foldable, Traversable, Generic)
instance NFData s => NFData (Quaternion s)
instance Arbitrary s => Arbitrary (Quaternion s) where arbitrary = Quaternion <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
instance Approx s => Approx (Quaternion s) where
  approx absdelta reldelta (Quaternion a b c d) (Quaternion a' b' c' d') = approx absdelta reldelta [a,b,c,d] [a',b',c',d']

-- TODO: not a list but a V.Vector?
newtype Matrix s = Matrix [[s]]
  deriving (Show, Functor, Foldable, Traversable)
  deriving (Approx, Arbitrary, NFData) via [[s]]

newtype Vector s = Vector [s]
  deriving (Show, Functor, Foldable, Traversable)
  deriving (Approx, Arbitrary, NFData) via [s]


-- Input types for the benchmark functions.

newtype FMult s = MkFMult (s, s)
  deriving (Show, Functor, Foldable, Traversable)
  deriving (Approx, Arbitrary, NFData) via (s, s)

newtype FDotProd s = FDotProd ([s], [s])
  deriving (Show, Functor, Foldable, Traversable)
  deriving (Approx, Arbitrary, NFData) via ([s], [s])

newtype FSumMatVec s = FSumMatVec ([[s]], [s])
  deriving (Show, Functor, Foldable, Traversable)
  deriving (Approx, Arbitrary, NFData) via ([[s]], [s])

newtype FRotVecQuat s = FRotVecQuat (Vec3 s, Quaternion s)
  deriving (Show, Functor, Foldable, Traversable)
  deriving (Approx, Arbitrary, NFData) via (Vec3 s, Quaternion s)

newtype FParticles s = FParticles [((s, s), (s, s))]
  deriving (Show, Functor, Foldable, Traversable)
  deriving (Approx, Arbitrary, NFData) via [((s, s), (s, s))]

-- - A list of layers (weights, bias);
-- - The input.
newtype FNeural s = FNeural ([(Matrix s, Vector s)], Vector s)
  deriving (Show, Functor, Foldable, Traversable)
  deriving (Approx, Arbitrary, NFData) via ([(Matrix s, Vector s)], Vector s)
