{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-| This separate module exists and is not inlined in "Main" solely because of
    the GHC stage restriction: 'reverseADandControl' needs to be defined in a
    separate module from where it is used. -}
module ControlFun where

import Language.Haskell.TH (Q, Code, Type)
import Language.Haskell.TH.Syntax (unTypeCode, unsafeCodeCoerce)
import Test.QuickCheck

import FinDiff
import Language.Haskell.ReverseAD.TH
import Test.Approx


newtype ControlFun a b = ControlFun (forall s. (Floating s, Ord s) => ReplaceElements a s -> ReplaceElements b s)

reverseADandControl
  :: forall a b.
     Q Type  -- ^ a
  -> Q Type  -- ^ b
  -> Code Q (a -> b)
  -> Code Q (a -> (b, b -> a), ControlFun a b)
reverseADandControl inpStruc outStruc program =
  -- The code coercion here goes from `a -> b` to
  -- `ReplaceElements a s -> ReplaceElements b s`, which is fine if the
  -- function is suitably generic over the scalar type. Which is the whole
  -- point of using dual-numbers AD.
  [|| ($$(reverseAD' (deriveStructureT inpStruc) (deriveStructureT outStruc) program)
      ,ControlFun $$(unsafeCodeCoerce (unTypeCode program))) ||]

newtype WeirdType a b = MkWeirdType (Int, [(a, b)])
  deriving (Show)

dataFinDiff ''WeirdType

instance (Arbitrary a, Arbitrary b) => Arbitrary (WeirdType a b) where
  arbitrary = MkWeirdType <$> arbitrary

instance (Approx a, Approx b) => Approx (WeirdType a b) where
  approx absdelta reldelta (MkWeirdType (_, l)) (MkWeirdType (_, l')) = approx absdelta reldelta l l'
