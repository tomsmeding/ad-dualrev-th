{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE ViewPatterns #-}
module Language.Haskell.ReverseAD where

import Data.Int
import Data.Proxy
import Data.Word
import Language.Haskell.TH


data Structure = SDiscrete | SScalar | STuple [Structure]
  deriving (Show)

-- TODO: use 'Language.Haskell.TH.reifyType' for this
class KnownStructure a where knownStructure :: Proxy a -> Structure
instance KnownStructure Int where knownStructure _ = SDiscrete
instance KnownStructure Int8 where knownStructure _ = SDiscrete
instance KnownStructure Int16 where knownStructure _ = SDiscrete
instance KnownStructure Int32 where knownStructure _ = SDiscrete
instance KnownStructure Int64 where knownStructure _ = SDiscrete
instance KnownStructure Word where knownStructure _ = SDiscrete
instance KnownStructure Word8 where knownStructure _ = SDiscrete
instance KnownStructure Word16 where knownStructure _ = SDiscrete
instance KnownStructure Word32 where knownStructure _ = SDiscrete
instance KnownStructure Word64 where knownStructure _ = SDiscrete
instance KnownStructure () where knownStructure _ = SDiscrete
instance KnownStructure Float where knownStructure _ = SScalar
instance KnownStructure Double where knownStructure _ = SScalar
instance (KnownStructure a, KnownStructure b) => KnownStructure (a, b) where
  knownStructure _ = STuple [knownStructure (Proxy @a), knownStructure (Proxy @b)]
instance (KnownStructure a, KnownStructure b, KnownStructure c) => KnownStructure (a, b, c) where
  knownStructure _ = STuple [knownStructure (Proxy @a), knownStructure (Proxy @b), knownStructure (Proxy @c)]
instance (KnownStructure a, KnownStructure b, KnownStructure c, KnownStructure d) => KnownStructure (a, b, c, d) where
  knownStructure _ = STuple [knownStructure (Proxy @a), knownStructure (Proxy @b), knownStructure (Proxy @c), knownStructure (Proxy @d)]

data Backpropagator a = Zero | Contribs [(a, Int)]
  deriving (Show)

-- | Use as follows:
--
--     > :t $$(reverseAD [|| \(x, y) -> x * y :: Double ||])
--     (Double, Double) -> (Double, Double -> (Double, Double))
reverseAD :: forall a b. (KnownStructure a, KnownStructure b)
          => Code Q (a -> b)
          -> Code Q (a -> (b, b -> a))
reverseAD (examineCode -> inputCode) =
  unsafeCodeCoerce $ do
    ex <- unType <$> inputCode
    transform (knownStructure (Proxy @a)) (knownStructure (Proxy @b)) ex

transform :: Structure -> Structure -> Exp -> Q Exp
transform _ _ _ = undefined

data NumOp2 = Add | Sub | Mul
  deriving (Show)

data NumOp1 = Negate
  deriving (Show)

class DiffNum a where
  type DiffNumDual a = r | r -> a
  applyNum2 :: NumOp2 -> DiffNumDual a -> DiffNumDual a -> DiffNumDual a
  applyNum1 :: NumOp1 -> DiffNumDual a -> DiffNumDual a

instance DiffNum Int where
  type DiffNumDual Int = Int
  applyNum2 Add x y = x + y
  applyNum2 Sub x y = x - y
  applyNum2 Mul x y = x * y
  applyNum1 Negate x = negate x

instance DiffNum Double where
  type DiffNumDual Double = (Double, Backpropagator Double)
  applyNum2 Add (x, d1) (y, d2) = (x + y, `-`)
  applyNum2 Sub x y = x - y
  applyNum2 Mul x y = x * y
  applyNum1 Negate x = negate x

ddr :: Name -> Exp -> Q Exp
ddr idName = \case
  VarE name -> return (TupE [Just (VarE name), Just (VarE idName)])
  ConE name -> fail $ "Data constructors not supported in reverseAD: " ++ show name
  LitE lit -> case lit of
    RationalL _ -> return (TupE [Just (TupE [Just (LitE lit), Just (ConE 'Zero)])
                                ,Just (VarE idName)])
    FloatPrimL _ -> fail "float prim?"
    DoublePrimL _ -> fail "double prim?"
    _ -> return (TupE [Just (LitE lit), Just (VarE idName)])
  AppE e1 e2 -> do
    e1' <- ddr idName e1
    idName1 <- newName "i"
    e2' <- ddr idName1 e2
    idName2 <- newName "i"
    funname <- newName "f"
    argname <- newName "a"
    return (LetE [ValD (TupP [VarP funname, VarP idName1]) (NormalB e1') []
                 ,ValD (TupP [VarP argname, VarP idName2]) (NormalB e2') []]
              (TupE [Just (AppE (VarE funname) (VarE argname)), Just (VarE idName2)]))
  InfixE (Just e1) (VarE opname) (Just e2) -> do
    e1' <- ddr idName e1
    idName1 <- newName "i"
    e2' <- ddr idName1 e2
    idName2 <- newName "i"
    x1name <- newName "x"
    x2name <- newName "y"
    if | opname == '(+) -> _

numberInput :: Structure -> Exp -> Integer -> Q (Integer, Exp)
numberInput struc input nextid = case struc of
  SDiscrete -> return (nextid, input)
  SScalar -> return
    (succ nextid
    ,TupE [Just input
          ,Just (ConE 'Contribs
                 `AppE` ListE [TupE [Just (LitE (RationalL 1.0))
                                    ,Just (LitE (IntegerL nextid))]])])
  STuple strucs -> do
    names <- mapM (const (newName "x")) strucs
    (nextid', exps) <-
      mapAccumLM (\nextid' (s, name) -> numberInput s (VarE name) nextid')
                 nextid (zip strucs names)
    return (nextid'
           ,LetE [ValD (TupP (map VarP names)) (NormalB input) []]
                 (TupE (map Just exps)))

mapAccumLM :: Monad m => (s -> a -> m (s, b)) -> s -> [a] -> m (s, [b])
mapAccumLM _ s0 [] = return (s0, [])
mapAccumLM f s0 (x:xs) = do (s1, y) <- f s0 x  -- TODO make this tail-recursive
                            (s2, ys) <- mapAccumLM f s1 xs
                            return (s2, y : ys)
