{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-| This separate module exists and is not inlined in "Main" solely because of
    the GHC stage restriction: 'reverseADandControl' needs to be defined in a
    separate module from where it is used. -}
module ControlFun where

import Data.Monoid (Sum(..))
import Language.Haskell.TH (Q, Code)
import Language.Haskell.TH.Syntax (unTypeCode, unsafeCodeCoerce)

import FinDiff
import Language.Haskell.ReverseAD.TH


newtype ControlFun a b = ControlFun (forall s. (Floating s, Ord s) => ReplaceElements a s -> ReplaceElements b s)

reverseADandControl
  :: forall a b. (KnownStructure a, KnownStructure b)
  => Code Q (a -> b)
  -> Code Q (a -> (b, b -> a), ControlFun a b)
reverseADandControl program =
  -- The code coercion here goes from `a -> b` to
  -- `ReplaceElements a s -> ReplaceElements b s`, which is fine if the
  -- function is suitably generic over the scalar type. Which is the whole
  -- point of using forward AD.
  [|| ($$(reverseAD program)
      ,ControlFun $$(unsafeCodeCoerce (unTypeCode program))) ||]

useTypeForReverseAD ''Sum
