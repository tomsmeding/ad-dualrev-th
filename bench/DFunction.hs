{-| This separate module exists and is not inlined in "Main" solely because of
    the GHC stage restriction: 'makeFunction' needs to be defined in a
    separate module from where it is used. -}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
module DFunction where

import Language.Haskell.TH (Q, Code, unsafeCodeCoerce, unTypeCode)

import qualified Numeric.AD as AD
import qualified Language.Haskell.ReverseAD.TH as DR


data DFunction f = DFunction
  { funOriginal :: forall s. (Floating s, Ord s) => f s -> s
  , radWithTH :: f Double -> (Double, f Double) }

newtype GenericFunction f = GenericFunction
  { runGF :: forall s. (Floating s, Ord s) => f s -> s }

makeFunction :: forall f.
                DR.KnownType (f Double)
             => Code Q (f Double -> Double)
             -> Code Q (DFunction f)
makeFunction code =
  let code1 = unsafeCodeCoerce [| GenericFunction $(unTypeCode code) |] :: Code Q (GenericFunction f)
  in [|| DFunction
           { funOriginal = runGF $$(code1)
           , radWithTH = \x ->
               case $$(DR.reverseAD [|| \y -> $$(code) y ||]) x of
                 (out, df) -> (out, df 1.0) } ||]

radWithAD :: Traversable f => DFunction f -> f Double -> (Double, f Double)
radWithAD fun = AD.grad' (\x -> funOriginal fun x)
