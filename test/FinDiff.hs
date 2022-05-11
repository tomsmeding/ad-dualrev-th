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

import Control.Monad (when, forM)
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

dataFinDiff :: Name -> Q [Dec]
dataFinDiff tyname = do
  extok <- and <$> traverse isExtEnabled [ScopedTypeVariables, TypeApplications]
  when (not extok) $
    fail "The instance declaration generated by dataFinDiff needs these extensions enabled:\n\
         \  ScopedTypeVariables, TypeApplications"

  -- We put the number of fields in 'constrs' simply to have that number easily
  -- available as 'n' in the long-winded instance body construction below.
  (tyvars, constrs) <- reify tyname >>= \case
    TyConI (NewtypeD [] _ tvbs _ constr _) -> do
      case constr of
        NormalC conname [(_, fieldty)] -> return (map tvbName tvbs, [(1, conname, [fieldty])])
        RecC conname [(_, _, fieldty)] -> return (map tvbName tvbs, [(1, conname, [fieldty])])
        _ -> fail "dataFinDiff: Unknown newtype form"

    TyConI (DataD [] _ tvbs _ constrs _) -> do
      constrs' <- forM constrs $ \case
        NormalC conname fieldtys -> return (length fieldtys, conname, [t | (_, t) <- fieldtys])
        RecC conname fieldtys -> return (length fieldtys, conname, [t | (_, _, t) <- fieldtys])
        _ -> fail "dataFinDiff: Multiple data constructors not yet supported"
      return (map tvbName tvbs, constrs')

    _ -> fail "dataFinDiff: Not newtype or data"

  let maxnfields = maximum [n | (n, _, _) <- constrs]
  valuevar <- newName "value"
  refvaluevar <- newName "refvalue"
  svar <- newName "s"
  xvars <- mapM (\i -> newName ("x" ++ show i)) [1 .. maxnfields]
  refvars <- mapM (\i -> newName ("ref" ++ show i)) [1 .. maxnfields]
  pvar <- newName "p"
  eltsvar <- newName "elts"
  lvars <- mapM (\i -> newName ("l" ++ show i)) [1 .. maxnfields]
  fvar <- newName "f"

  let funD' name pats body = FunD name [Clause pats (NormalB body) []]

  let context = map (\tyvar -> ConT ''FinDiff `AppT` VarT tyvar) tyvars
                ++ map (\tyvar -> EqualityT `AppT` (ConT ''Element `AppT` VarT tyvar)
                                            `AppT` ConT ''Double)
                       tyvars
      targetType = foldl' AppT (ConT tyname) (map VarT tyvars)
      replacedType = foldl' AppT (ConT tyname) (map (\n -> ConT ''ReplaceElements `AppT` VarT n `AppT` VarT svar) tyvars)
      body =
        [TySynInstD (TySynEqn Nothing (ConT ''Element `AppT` targetType)
                                      (case tyvars of
                                         [] -> ConT ''Double
                                         tv:_ -> ConT ''Element `AppT` VarT tv))
        ,TySynInstD (TySynEqn Nothing (ConT ''ReplaceElements `AppT` targetType `AppT` VarT svar) replacedType)
        ,funD' 'elements' [WildP, VarP valuevar] $
           CaseE (VarE valuevar)
             [Match (ConP conname [] (map VarP (take n xvars)))
                    (NormalB $
                       VarE 'concat `AppE` ListE
                         [VarE 'elements'
                            `AppE` (ConE 'Proxy `AppTypeE` fieldty)
                            `AppE` VarE xvar
                         | (fieldty, xvar) <- zip fieldtys xvars])
                    []
             | (n, conname, fieldtys) <- constrs]
        ,funD' 'rebuild' [WildP, VarP pvar, VarP refvaluevar, VarP eltsvar] $
           CaseE (VarE refvaluevar)
             [Match (ConP conname [] (map VarP (take n refvars)))
                    (NormalB $
                       LetE [ValD (TupP [VarP xvar, VarP lvar])
                                  (NormalB (VarE 'rebuild'
                                              `AppE` (ConE 'Proxy `AppTypeE` fieldty)
                                              `AppE` VarE pvar
                                              `AppE` VarE refvar
                                              `AppE` VarE prevlvar))
                                  []
                            | (xvar, lvar, refvar, prevlvar, fieldty)
                                 <- zip5 xvars lvars refvars (eltsvar : lvars) fieldtys] $
                         TupE [Just (foldl' AppE (ConE conname) (map VarE (take n xvars)))
                              ,Just (VarE ((eltsvar:lvars) !! n))])
                    []
             | (n, conname, fieldtys) <- constrs]
        ,funD' 'oneElement [WildP] $
           case tyvars of
             [] -> LitE (IntegerL 1)
             tv:_ -> VarE 'oneElement `AppE` (ConE 'Proxy `AppTypeE` VarT tv)
        ,funD' 'zero [VarP pvar, VarP refvaluevar] $
           CaseE (VarE refvaluevar)
             [Match (ConP conname [] (map VarP (take n refvars)))
                    (NormalB $
                       foldl' AppE (ConE conname)
                         [VarE 'zero `AppE` VarE pvar `AppE` VarE refvar
                         | refvar <- take n refvars])
                    []
             | (n, conname, _) <- constrs]
        ,funD' 'replaceElements [WildP, VarP fvar, VarP valuevar] $
           CaseE (VarE valuevar)
             [Match (ConP conname [] (map VarP (take n xvars)))
                    (NormalB $
                       foldl' AppE (ConE conname)
                         [VarE 'replaceElements
                            `AppE` (ConE 'Proxy `AppTypeE` fieldty)
                            `AppE` VarE fvar
                            `AppE` VarE xvar
                         | (xvar, fieldty) <- zip xvars fieldtys])
                    []
             | (n, conname, fieldtys) <- constrs]
        ,FunD 'replaceElementsId
           [Clause []
                   (GuardedB [(PatG [BindS (ConP 'Refl [] [])
                                           (VarE 'replaceElementsId `AppTypeE` VarT tyvar)
                                    | tyvar <- tyvars]
                              ,ConE 'Refl)])
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
