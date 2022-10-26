{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS -Wno-orphans #-}
module Types where

import Data.Monoid (Sum(..))
import Test.QuickCheck

import FinDiff
import Test.Approx


newtype WeirdType a b = MkWeirdType (Int, [(a, b)]) deriving (Show)
dataFinDiff ''WeirdType
instance (Arbitrary a, Arbitrary b) => Arbitrary (WeirdType a b) where arbitrary = MkWeirdType <$> arbitrary
instance (Approx a, Approx b) => Approx (WeirdType a b) where approx absdelta reldelta (MkWeirdType (_, l)) (MkWeirdType (_, l')) = approx absdelta reldelta l l'

data Vec3 a = Vec3 a a a deriving (Show)
dataFinDiff ''Vec3
instance Arbitrary a => Arbitrary (Vec3 a) where arbitrary = Vec3 <$> arbitrary <*> arbitrary <*> arbitrary
instance Approx a => Approx (Vec3 a) where approx absdelta reldelta (Vec3 a b c) (Vec3 a' b' c') = approx absdelta reldelta [a, b, c] [a', b', c']

data Quaternion a = Quaternion a a a a deriving (Show)
dataFinDiff ''Quaternion
instance Arbitrary a => Arbitrary (Quaternion a) where arbitrary = Quaternion <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
instance Approx a => Approx (Quaternion a) where approx absdelta reldelta (Quaternion a b c d) (Quaternion a' b' c' d') = approx absdelta reldelta [a, b, c, d] [a', b', c', d']

newtype Vec3N a = Vec3N (a, a, a) deriving (Show)
dataFinDiff ''Vec3N
instance Arbitrary a => Arbitrary (Vec3N a) where arbitrary = Vec3N <$> arbitrary
instance Approx a => Approx (Vec3N a) where approx absdelta reldelta (Vec3N (a, b, c)) (Vec3N (a', b', c')) = approx absdelta reldelta [a, b, c] [a', b', c']

newtype QuaternionN a = QuaternionN (a, a, a, a) deriving (Show)
dataFinDiff ''QuaternionN
instance Arbitrary a => Arbitrary (QuaternionN a) where arbitrary = QuaternionN <$> arbitrary
instance Approx a => Approx (QuaternionN a) where approx absdelta reldelta (QuaternionN (a, b, c, d)) (QuaternionN (a', b', c', d')) = approx absdelta reldelta [a, b, c, d] [a', b', c', d']

data WeirdSum a b = WSOne a Int a | WSTwo (b, a) deriving (Show)
dataFinDiff ''WeirdSum
instance (Arbitrary a, Arbitrary b) => Arbitrary (WeirdSum a b) where
  arbitrary = oneof [WSOne <$> arbitrary <*> arbitrary <*> arbitrary
                    ,WSTwo <$> arbitrary]
instance (Approx a, Approx b) => Approx (WeirdSum a b) where
  approx absdelta reldelta (WSOne a i b) (WSOne a' i' b') =
    approx absdelta reldelta ([a, b], i) ([a', b'], i')
  approx absdelta reldelta (WSTwo a) (WSTwo a') =
    approx absdelta reldelta a a'
  approx _ _ _ _ = False

dataFinDiff ''Sum

data AltList1 a = AltCons1 a (AltList2 a) | AltNil1
  deriving (Show, Functor)
data AltList2 a = AltCons2 a (AltList1 a) | AltNil2
  deriving (Show, Functor)
-- Need to generate these instances simultaneously because they reference each
-- other, and TH splices split up the file into distinct units for type
-- inference.
dataFinDiffs [''AltList1, ''AltList2]
instance Arbitrary a => Arbitrary (AltList1 a) where arbitrary = oneof [AltCons1 <$> arbitrary <*> arbitrary, pure AltNil1]
instance Arbitrary a => Arbitrary (AltList2 a) where arbitrary = oneof [AltCons2 <$> arbitrary <*> arbitrary, pure AltNil2]
instance Approx a => Approx (AltList1 a) where
  approx absdelta reldelta (AltCons1 a b) (AltCons1 a' b') = approx absdelta reldelta (a, b) (a', b')
  approx _ _ AltNil1 AltNil1 = True
  approx _ _ _ _ = False
instance Approx a => Approx (AltList2 a) where
  approx absdelta reldelta (AltCons2 a b) (AltCons2 a' b') = approx absdelta reldelta (a, b) (a', b')
  approx _ _ AltNil2 AltNil2 = True
  approx _ _ _ _ = False

instance Foldable AltList1 where
  foldMap f (AltCons1 x l) = f x <> foldMap f l
  foldMap _ AltNil1 = mempty
instance Foldable AltList2 where
  foldMap f (AltCons2 x l) = f x <> foldMap f l
  foldMap _ AltNil2 = mempty
