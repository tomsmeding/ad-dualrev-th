{-| This separate module exists and is not inlined in "Main" solely because of
    the GHC stage restriction: 'makeFunction' needs to be defined in a
    separate module from where it is used. -}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
module DFunction where

import Language.Haskell.TH (Quote, Code)

import qualified Numeric.AD as AD
import qualified Language.Haskell.ReverseAD.TH as DR


data DFunction f = DFunction
  { funOriginal :: forall s. (Floating s, Ord s) => f s -> s
  , radWithTH :: f Double -> (Double, f Double) }

newtype GenericFunction f = GenericFunction
  { runGF :: forall s. (Floating s, Ord s) => f s -> s }

makeFunction :: (DR.KnownStructure (f Double), Quote m, MonadFail m)
             => Code m (GenericFunction f)
             -> Code m (DFunction f)
makeFunction code =
  [|| DFunction
        { funOriginal = runGF $$(code)
        , radWithTH = \x ->
            case $$(DR.reverseAD [|| \y -> case $$(code) of GenericFunction f -> f y ||]) x of
              (out, df) -> (out, df 1.0) } ||]

radWithAD :: Traversable f => DFunction f -> f Double -> (Double, f Double)
radWithAD fun = AD.grad' (\x -> funOriginal fun x)
