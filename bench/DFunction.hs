{-| This separate module exists and is not inlined in "Main" solely because of
    the GHC stage restriction: 'makeFunction' needs to be defined in a
    separate module from where it is used. -}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
module DFunction (
  DFunction,
  radWithTH,
  radWithAD,
  makeFunction,
) where

import Data.Bifunctor (second)
import Language.Haskell.TH (Q, Code, unsafeCodeCoerce, unTypeCode)

import qualified Numeric.AD as AD
import qualified Language.Haskell.ReverseAD.TH as DR


class ZeroOne a where zero :: a ; one :: a
instance ZeroOne Double where zero = 0.0 ; one = 1.0

newtype IdGen a = IdGen { runIdGen :: Int -> (Int, a) } deriving (Functor)
instance Applicative IdGen where
  pure x = IdGen (\i -> (i, x))
  IdGen f <*> IdGen g = IdGen (\i -> let (i', fun) = f i
                                     in fun <$> g i')
genId :: IdGen Int
genId = IdGen (\i -> (succ i, i))

-- | Given a structure of values, return a structure that joins, to each
-- value, a structure with the same shape as the input, but filled with
-- 'zero' in the other positions and with 'one' in the current, focused
-- position.
oneHots :: (Traversable f, ZeroOne a) => f a -> f (a, f a)
oneHots struc =
  let (_, ixstruc) = runIdGen (traverse (\x -> (x,) <$> genId) struc) 0
  in fmap (\(x, i) -> (x, (delta i . snd) <$> ixstruc))
          ixstruc
  where delta i j | i == j = one
                  | otherwise = zero


data DFunction f g = DFunction
  { funOriginal :: forall s. (Floating s, Ord s) => f s -> g s
  , radWithTH :: f Double -> g (Double, f Double) }

newtype GenericFunction f g = GenericFunction
  { runGF :: forall s. (Floating s, Ord s) => f s -> g s }

makeFunction :: forall f g.
                (DR.KnownType (f Double), DR.KnownType (g Double), Traversable g)
             => Code Q (f Double -> g Double)
             -> Code Q (DFunction f g)
makeFunction code =
  let code1 = unsafeCodeCoerce [| GenericFunction $(unTypeCode code) |] :: Code Q (GenericFunction f g)
  in [|| DFunction
           { funOriginal = runGF $$(code1)
           , radWithTH = \x ->
               case $$(DR.reverseAD [|| \y -> $$(code) y ||]) x of
                 (out, df) -> second df <$> oneHots out } ||]

radWithAD :: (Traversable f, Functor g) => DFunction f g -> f Double -> g (Double, f Double)
radWithAD fun = AD.jacobian' (\x -> funOriginal fun x)
