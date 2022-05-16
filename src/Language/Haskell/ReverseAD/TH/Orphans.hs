{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS -Wno-orphans #-}
module Language.Haskell.ReverseAD.TH.Orphans where

import Data.Map.Internal (Map(..))

import Language.Haskell.TH.Syntax


deriving instance Lift OccName
deriving instance Lift NameSpace
deriving instance Lift PkgName
deriving instance Lift ModName
deriving instance Lift NameFlavour
deriving instance Lift Name
deriving instance (Lift k, Lift a) => Lift (Map k a)

data SRT1 a = A Int (SRT2 a) | B Double
  deriving (Show)

data SRT2 a = C (SRT1 a) Double
  deriving (Show)
