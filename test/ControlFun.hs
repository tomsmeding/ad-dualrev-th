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

import Data.Monoid (Sum(..))
import Data.Proxy
import Data.Type.Equality
import Language.Haskell.TH (Q, Code, Type)
import Language.Haskell.TH.Syntax (unTypeCode, unsafeCodeCoerce)
import Test.QuickCheck

import FinDiff
import Language.Haskell.ReverseAD.TH


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

-- useTypeForReverseAD ''Sum

newtype WeirdType a b = MkWeirdType (Int, [(a, b)])
  deriving (Show)

-- useTypeForReverseAD ''WeirdType

instance (FinDiff a, FinDiff b, Element a ~ Element b) => FinDiff (WeirdType a b) where
  type Element (WeirdType a b) = Element a
  type ReplaceElements (WeirdType a b) s = WeirdType (ReplaceElements a s) (ReplaceElements b s)
  elements' _ (MkWeirdType (_, l)) = elements' (Proxy @[(a, b)]) l
  rebuild' _ p (MkWeirdType (refn, refl)) elts =
    let (l, rest) = rebuild' (Proxy @[(a, b)]) p refl elts in (MkWeirdType (refn, l), rest)
  oneElement _ = oneElement (Proxy @a)
  zero p (MkWeirdType (refn, ref)) = MkWeirdType (refn, zero p ref)
  replaceElements _ f (MkWeirdType (n, l)) = MkWeirdType (n, replaceElements (Proxy @[(a, b)]) f l)
  replaceElementsId | Refl <- replaceElementsId @[(a, b)] = Refl

instance (Arbitrary a, Arbitrary b) => Arbitrary (WeirdType a b) where
  arbitrary = MkWeirdType <$> arbitrary
