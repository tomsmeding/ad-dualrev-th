{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS -Wno-orphans #-}
module Types where

import Data.Monoid (Sum(..))
import Language.Haskell.ReverseAD.TH
import Test.QuickCheck

import FinDiff
import Test.Approx


newtype WeirdType a b = MkWeirdType (Int, [(a, b)]) deriving (Show)
dataFinDiff ''WeirdType
makeKnownType ''WeirdType
instance (Arbitrary a, Arbitrary b) => Arbitrary (WeirdType a b) where arbitrary = MkWeirdType <$> arbitrary
instance (Approx a, Approx b) => Approx (WeirdType a b) where approx absdelta reldelta (MkWeirdType (_, l)) (MkWeirdType (_, l')) = approx absdelta reldelta l l'

data Vec3 a = Vec3 a a a deriving (Show)
dataFinDiff ''Vec3
makeKnownType ''Vec3
instance Arbitrary a => Arbitrary (Vec3 a) where arbitrary = Vec3 <$> arbitrary <*> arbitrary <*> arbitrary
instance Approx a => Approx (Vec3 a) where approx absdelta reldelta (Vec3 a b c) (Vec3 a' b' c') = approx absdelta reldelta [a, b, c] [a', b', c']

data Quaternion a = Quaternion a a a a deriving (Show)
dataFinDiff ''Quaternion
makeKnownType ''Quaternion
instance Arbitrary a => Arbitrary (Quaternion a) where arbitrary = Quaternion <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
instance Approx a => Approx (Quaternion a) where approx absdelta reldelta (Quaternion a b c d) (Quaternion a' b' c' d') = approx absdelta reldelta [a, b, c, d] [a', b', c', d']

newtype Vec3N a = Vec3N (a, a, a) deriving (Show)
dataFinDiff ''Vec3N
makeKnownType ''Vec3N
instance Arbitrary a => Arbitrary (Vec3N a) where arbitrary = Vec3N <$> arbitrary
instance Approx a => Approx (Vec3N a) where approx absdelta reldelta (Vec3N (a, b, c)) (Vec3N (a', b', c')) = approx absdelta reldelta [a, b, c] [a', b', c']

newtype QuaternionN a = QuaternionN (a, a, a, a) deriving (Show)
dataFinDiff ''QuaternionN
makeKnownType ''QuaternionN
instance Arbitrary a => Arbitrary (QuaternionN a) where arbitrary = QuaternionN <$> arbitrary
instance Approx a => Approx (QuaternionN a) where approx absdelta reldelta (QuaternionN (a, b, c, d)) (QuaternionN (a', b', c', d')) = approx absdelta reldelta [a, b, c, d] [a', b', c', d']

makeKnownType ''Sum
