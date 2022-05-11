{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS -Wno-orphans #-}
module Language.Haskell.ReverseAD.TH.Orphans where

import Language.Haskell.TH.Syntax


deriving instance Lift OccName
deriving instance Lift NameSpace
deriving instance Lift PkgName
deriving instance Lift ModName
deriving instance Lift NameFlavour
deriving instance Lift Name
