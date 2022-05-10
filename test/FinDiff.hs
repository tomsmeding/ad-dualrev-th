{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
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
  FinDiff(..),
  dataFinDiff,
) where

import Control.Monad (zipWithM, when)
import Data.Monoid (Sum(..))
import Data.Proxy
import Data.List (transpose, foldl', zip5)
-- import qualified Data.Vector as V
import Data.Type.Equality
import Language.Haskell.TH


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

-- | Element type is assumed to be Double
instance FinDiff Int where
  type Element Int = Double
  type ReplaceElements Int s = Int
  elements' _ _ = []
  rebuild' _ _ n l = (n, l)
  oneElement _ = 1.0
  zero _ n = n
  replaceElements _ _ n = n
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

instance (FinDiff a, FinDiff b, FinDiff c, Element a ~ Element b, Element a ~ Element c) => FinDiff (a, b, c) where
  type Element (a, b, c) = Element a
  type ReplaceElements (a, b, c) s = (ReplaceElements a s, ReplaceElements b s, ReplaceElements c s)
  elements' _ (x, y, z) = elements' (Proxy @a) x ++ elements' (Proxy @b) y ++ elements' (Proxy @c) z
  rebuild' _ p (refx, refy, refz) l =
    let (x, l1) = rebuild' (Proxy @a) p refx l
        (y, l2) = rebuild' (Proxy @b) p refy l1
        (z, l3) = rebuild' (Proxy @c) p refz l2
    in ((x, y, z), l3)
  oneElement _ = oneElement (Proxy @a)
  zero p (refx, refy, refz) = (zero p refx, zero p refy, zero p refz)
  replaceElements _ f (x, y, z) = (replaceElements (Proxy @a) f x, replaceElements (Proxy @b) f y, replaceElements (Proxy @c) f z)
  replaceElementsId
    | Refl <- replaceElementsId @a
    , Refl <- replaceElementsId @b
    , Refl <- replaceElementsId @c
    = Refl

instance (FinDiff a, FinDiff b, FinDiff c, FinDiff d, Element a ~ Element b, Element a ~ Element c, Element a ~ Element d) => FinDiff (a, b, c, d) where
  type Element (a, b, c, d) = Element a
  type ReplaceElements (a, b, c, d) s = (ReplaceElements a s, ReplaceElements b s, ReplaceElements c s, ReplaceElements d s)
  elements' _ (x, y, z, w) = elements' (Proxy @a) x ++ elements' (Proxy @b) y ++ elements' (Proxy @c) z ++ elements' (Proxy @d) w
  rebuild' _ p (refx, refy, refz, refw) l =
    let (x, l1) = rebuild' (Proxy @a) p refx l
        (y, l2) = rebuild' (Proxy @b) p refy l1
        (z, l3) = rebuild' (Proxy @c) p refz l2
        (w, l4) = rebuild' (Proxy @d) p refw l3
    in ((x, y, z, w), l4)
  oneElement _ = oneElement (Proxy @a)
  zero p (refx, refy, refz, refw) = (zero p refx, zero p refy, zero p refz, zero p refw)
  replaceElements _ f (x, y, z, w) = (replaceElements (Proxy @a) f x, replaceElements (Proxy @b) f y, replaceElements (Proxy @c) f z, replaceElements (Proxy @d) f w)
  replaceElementsId
    | Refl <- replaceElementsId @a
    , Refl <- replaceElementsId @b
    , Refl <- replaceElementsId @c
    , Refl <- replaceElementsId @d
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

dataFinDiff :: Name -> Q [Dec]
dataFinDiff tyname = do
  extok <- and <$> traverse isExtEnabled [ScopedTypeVariables, TypeApplications]
  when (not extok) $
    fail "The instance declaration generated by dataFinDiff needs these extensions enabled:\n\
         \  ScopedTypeVariables, TypeApplications"

  (tyvars, conname, fieldtys) <- reify tyname >>= \case
    TyConI (NewtypeD [] _ tvbs _ constr _) -> do
      case constr of
        NormalC conname [(_, fieldty)] -> return (map tvbName tvbs, conname, [fieldty])
        RecC conname [(_, _, fieldty)] -> return (map tvbName tvbs, conname, [fieldty])
        _ -> fail "dataFinDiff: Unknown newtype form"

    TyConI (DataD [] _ tvbs _ constrs _) -> do
      case constrs of
        [NormalC conname fieldtys] -> return (map tvbName tvbs, conname, [t | (_, t) <- fieldtys])
        [RecC conname fieldtys] -> return (map tvbName tvbs, conname, [t | (_, _, t) <- fieldtys])
        _ -> fail "dataFinDiff: Multiple data constructors not yet supported"

    _ -> fail "dataFinDiff: Not newtype or data"

  fieldty0 <- case fieldtys of
    [] -> fail "dataFinDiff: Empty data declarations not supported"
    t:_ -> return t

  svar <- newName "s"
  xvars <- mapM (\_ -> newName "x") fieldtys
  refvars <- mapM (\_ -> newName "ref") fieldtys
  pvar <- newName "p"
  eltsvar <- newName "elts"
  lvars <- zipWithM (\_ i -> newName ("l" ++ show i)) fieldtys [1::Int ..]
  fvar <- newName "f"

  let funD' name pats body = FunD name [Clause pats (NormalB body) []]

  let context = map (ConT ''FinDiff `AppT`) fieldtys
                ++ map (\t -> EqualityT `AppT` (ConT ''Element `AppT` t)
                                        `AppT` ConT ''Double)
                       fieldtys
      targetType = foldl' AppT (ConT tyname) (map VarT tyvars)
      replacedType = foldl' AppT (ConT tyname) (map (\n -> ConT ''ReplaceElements `AppT` VarT n `AppT` VarT svar) tyvars)
      body =
        [TySynInstD (TySynEqn Nothing (ConT ''Element `AppT` targetType) (ConT ''Element `AppT` fieldty0))
        ,TySynInstD (TySynEqn Nothing (ConT ''ReplaceElements `AppT` targetType `AppT` VarT svar) replacedType)
        ,funD' 'elements' [WildP, ConP conname [] (map VarP xvars)] $
           foldr1 (\a b -> InfixE (Just a) (VarE '(++)) (Just b))
             [VarE 'elements' `AppE` (ConE 'Proxy `AppTypeE` fieldty) `AppE` VarE xvar
             | (fieldty, xvar) <- zip fieldtys xvars]
        ,funD' 'rebuild' [WildP, VarP pvar, ConP conname [] (map VarP refvars), VarP eltsvar] $
           LetE [ValD (TupP [VarP xvar, VarP lvar])
                      (NormalB (VarE 'rebuild'
                                  `AppE` (ConE 'Proxy `AppTypeE` fieldty)
                                  `AppE` VarE pvar
                                  `AppE` VarE refvar
                                  `AppE` VarE prevlvar))
                      []
                | (xvar, lvar, refvar, prevlvar, fieldty) <- zip5 xvars lvars refvars (eltsvar : lvars) fieldtys] $
             TupE [Just (foldl' AppE (ConE conname) (map VarE xvars))
                  ,Just (VarE (last lvars))]
        ,funD' 'oneElement [WildP] $
           VarE 'oneElement `AppE` (ConE 'Proxy `AppTypeE` fieldty0)
        ,funD' 'zero [VarP pvar, ConP conname [] (map VarP refvars)] $
           foldl' AppE (ConE conname)
             [VarE 'zero `AppE` VarE pvar `AppE` VarE refvar
             | refvar <- refvars]
        ,funD' 'replaceElements [WildP, VarP fvar, ConP conname [] (map VarP xvars)] $
           foldl' AppE (ConE conname)
             [VarE 'replaceElements `AppE` (ConE 'Proxy `AppTypeE` fieldty) `AppE` VarE fvar `AppE` VarE xvar
             | (xvar, fieldty) <- zip xvars fieldtys]
        ,FunD 'replaceElementsId
           [Clause []
                   (GuardedB [(PatG [BindS (ConP 'Refl [] []) (VarE 'replaceElementsId `AppTypeE` fieldty)]
                              ,ConE 'Refl)
                             | fieldty <- fieldtys])
                   []]
        ]

  return $ pure $ InstanceD Nothing context (ConT ''FinDiff `AppT` targetType) body
  where
    tvbName (PlainTV n _) = n
    tvbName (KindedTV n _ _) = n

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
