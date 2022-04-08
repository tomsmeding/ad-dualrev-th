{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | Supporting definitions for finite differencing in the test suite, as well
-- as Jacobian computation using a function transformed with forward-ad,
-- reverse-ad or finite-differencing.
module FinDiff (
  jacobianByCols,
  jacobianByRows,
  jacobianByFinDiff,
  jacobianByElts,
  finiteDifference,
  FinDiff(..)
) where

import Data.Monoid (Sum(..))
import Data.Proxy
import Data.List (transpose)
-- import qualified Data.Vector as V
import Data.Type.Equality


class FinDiff a where
  type Element a
  type ReplaceElements a s
  elements' :: Proxy a -> ReplaceElements a s -> [s]

  -- | Given a reference object to glean the structure from, rebuilds a value
  -- from the prefix of the list. Returns any excess elements.
  rebuild' :: Proxy a -> Proxy s' -> ReplaceElements a s' -> [s] -> (ReplaceElements a s, [s])

  -- | The "one" element of the 'Element' type of this thing. For 'Double' this
  -- is @1.0@.
  oneElement :: Proxy a -> Element a

  -- | Given a reference object for structure
  zero :: Proxy s' -> ReplaceElements a s' -> a

  replaceElements :: Proxy a -> (s1 -> s2) -> ReplaceElements a s1 -> ReplaceElements a s2

  replaceElementsId :: ReplaceElements a (Element a) :~: a

  elements :: a -> [Element a]
  elements | Refl <- replaceElementsId @a = elements' (Proxy @a)

  -- | Given a reference object to glean the structure from, rebuild a value
  -- from the list of elements. Assumes that the list has the right length.
  rebuild :: Proxy s' -> ReplaceElements a s' -> [Element a] -> a
  rebuild p ref | Refl <- replaceElementsId @a = fst . rebuild' (Proxy @a) p ref

  -- | Given a reference object to glean the structure from, rebuild a value
  -- from a list of differently-typed elements. Assumes that the list has the
  -- right length.
  rebuildAs :: Proxy a -> Proxy s' -> ReplaceElements a s' -> [s] -> ReplaceElements a s
  rebuildAs p q ref = fst . rebuild' p q ref

  -- | Given a reference object for structure
  oneHotVecs :: Proxy s' -> ReplaceElements a s' -> [a]
  oneHotVecs p ref = go id (elements @a (zero p ref))
    where go :: FinDiff a => ([Element a] -> [Element a]) -> [Element a] -> [a]
          go _ [] = []
          go prefix (x:xs) = rebuild p ref (prefix (oneElement (Proxy @a) : xs)) : go (prefix . (x:)) xs

-- | Element type is assumed to be Double
instance FinDiff () where
  type Element () = Double
  type ReplaceElements () s = ()
  elements' _ () = []
  rebuild' _ _ () l = ((), l)
  oneElement _ = 1.0
  zero _ () = ()
  replaceElements _ _ () = ()
  replaceElementsId = Refl

instance (FinDiff a, FinDiff b, Element a ~ Element b) => FinDiff (a, b) where
  type Element (a, b) = Element a
  type ReplaceElements (a, b) s = (ReplaceElements a s, ReplaceElements b s)
  elements' _ (x, y) = elements' (Proxy @a) x ++ elements' (Proxy @b) y
  rebuild' _ p (refx, refy) l =
    let (x, l1) = rebuild' (Proxy @a) p refx l
        (y, l2) = rebuild' (Proxy @b) p refy l1
    in ((x, y), l2)
  oneElement _ = oneElement (Proxy @a)
  zero p (refx, refy) = (zero p refx, zero p refy)
  replaceElements _ f (x, y) = (replaceElements (Proxy @a) f x, replaceElements (Proxy @b) f y)
  replaceElementsId
    | Refl <- replaceElementsId @a
    , Refl <- replaceElementsId @b
    = Refl

instance FinDiff Double where
  type Element Double = Double
  type ReplaceElements Double s = s
  elements' _ x = [x]
  rebuild' _ _ _ l = (head l, tail l)
  oneElement _ = 1.0
  zero _ _ = 0.0
  replaceElements _ f x = f x
  replaceElementsId = Refl

-- instance KnownNat n => FinDiff (Vect n) where
--   type Element (Vect n) = Double
--   elements = V.toList
--   rebuild' l =
--     let (l1, l2) = splitAt (fromIntegral (natVal (Proxy @n))) l
--         Just v = V.fromList l1
--     in (v, l2)
--   oneElement _ = 1.0

instance FinDiff a => FinDiff [a] where
  type Element [a] = Element a
  type ReplaceElements [a] s = [ReplaceElements a s]
  elements' _ l = concatMap (elements' (Proxy @a)) l
  rebuild' _ _ [] elts = ([], elts)
  rebuild' _ p (refx:refxs) elts =
    let (x, elts') = rebuild' (Proxy @a) p refx elts
        (xs, elts'') = rebuild' (Proxy @[a]) p refxs elts'
    in (x : xs, elts'')
  oneElement _ = oneElement (Proxy @a)
  zero p refl = map (zero p) refl
  replaceElements _ f l = map (replaceElements (Proxy @a) f) l
  replaceElementsId | Refl <- replaceElementsId @a = Refl

instance FinDiff a => FinDiff (Sum a) where
  type Element (Sum a) = Element a
  type ReplaceElements (Sum a) s = Sum (ReplaceElements a s)
  elements' _ (Sum x) = elements' (Proxy @a) x
  rebuild' _ p (Sum ref) elts = let (x, rest) = rebuild' (Proxy @a) p ref elts in (Sum x, rest)
  oneElement _ = oneElement (Proxy @a)
  zero p (Sum ref) = Sum (zero p ref)
  replaceElements _ f (Sum x) = Sum (replaceElements (Proxy @a) f x)
  replaceElementsId | Refl <- replaceElementsId @a = Refl

-- | Given the reverse derivative of some function of type @a -> b@, return the
-- Jacobian of the function at the given input.
-- The first argument is a reference adjoint so that successful one-hot adjoint
-- can be generated.
jacobianByRows :: forall a b' a'. (FinDiff b', FinDiff a', Element a' ~ Double)
               => b' -> (a -> b' -> a') -> a -> [[Double]]
jacobianByRows refadj revad inp
  | Refl <- replaceElementsId @b'
  = [elements (revad inp adjoint) | adjoint <- oneHotVecs (Proxy @(Element b')) refadj]

-- | Given the forward derivative of some function of type @a -> b@, return the
-- Jacobian of the function at the given input.
jacobianByCols :: forall a b. (FinDiff a, FinDiff b, Element b ~ Double)
               => (a -> a -> b) -> a -> [[Double]]
jacobianByCols fwdad inp
  | Refl <- replaceElementsId @a
  = transpose [elements (fwdad inp tangent) | tangent <- oneHotVecs (Proxy @(Element a)) inp]

jacobianByFinDiff :: forall a b. (FinDiff a, FinDiff b, Element a ~ Double, Element b ~ Double)
                  => b -> (a -> b) -> a -> [[Double]]
jacobianByFinDiff refout f x = jacobianByElts refout (finiteDifference f) x

-- | Given a finite-differencing derivative of some function of type @a -> b@,
-- return the Jacobian of the function at the given input. The first argument
-- is a reference output value so that effective one-hot output adjoints can be
-- generated to this model.
--
-- The finite-differencing derivative takes three arguments: an input value
-- @x@, a one-hot input vector @v@, and a one-hot output vector @w@. Let @f@ be
-- the function that is to be differentiated. The output should be an estimate
-- of the partial derivative of the component of @f@ indicated by the
-- one-position in @w@, with respect to the input component indicated by the
-- one-position in @v@.
--
-- For finite-differencing, this means that a calculation similar to the
-- following is expected:
-- @1/h ((f(x + h v) - f(x)) `dot` w)@.
jacobianByElts :: forall a b. (FinDiff a, Element a ~ Double, FinDiff b, Element b ~ Double)
               => b -> (a -> a -> b -> Double) -> a -> [[Double]]
jacobianByElts refadj fd inp
  | Refl <- replaceElementsId @a
  , Refl <- replaceElementsId @b
  = [[fd inp v w | v <- oneHotVecs (Proxy @Double) inp]
    | w <- oneHotVecs (Proxy @Double) refadj]

-- | Compute a single element of the Jacobian of @f@ using finite differencing.
-- In the arguments @f@, @x@, @dx@, @dy@, the argument @x@ is the input value,
-- and @dx@ and @dy@ should respectively be one-hot vectors indicating the
-- column and row of the Jacobian, respectively.
--
-- This function is suitable to be used with 'jacobianByElts'.
finiteDifference :: forall a b. (FinDiff a, FinDiff b, Element a ~ Double, Element b ~ Double)
                 => (a -> b) -> a -> a -> b -> Double
finiteDifference f x dx dy
  | Refl <- replaceElementsId @a =
  let veczip :: forall a'. FinDiff a' => (Element a' -> Element a' -> Element a') -> a' -> a' -> a'
      veczip g a b | Refl <- replaceElementsId @a'
                   = rebuild (Proxy @(Element a')) a (zipWith g (elements a) (elements b))
      vecsum = sum . elements
      add = veczip (+)
      sub = veczip (-)
      dot a b = vecsum (veczip (*) a b)
      scale :: forall a'. (FinDiff a', Num (Element a')) => Element a' -> a' -> a'
      scale e a | Refl <- replaceElementsId @a'
                = veczip (*) (rebuild (Proxy @(Element a')) a (e <$ elements @a' (zero (Proxy @(Element a')) a))) a
  in recip h * ((f (x `add` scale h dx) `sub` f x) `dot` dy)
  where
    h = 0.000001 :: Double
