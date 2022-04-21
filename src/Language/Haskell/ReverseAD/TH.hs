{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS -Wno-incomplete-uni-patterns #-}
module Language.Haskell.ReverseAD.TH (
  reverseAD,
  reverseAD',
  -- useTypeForReverseAD,
  KnownType,
  Structure,
  knownStructure,
  deriveStructureT,
) where

import Control.Applicative (asum)
import Data.Bifunctor (first, second)
import Control.Monad (forM, zipWithM, when)
import Data.Foldable (toList)
import Data.Function ((&))
import Data.List (tails, mapAccumL)
import Data.Int
import Data.Proxy
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as V
import Data.Void
import Data.Word
import GHC.TypeLits (TypeError, ErrorMessage(Text))
import GHC.Types (Multiplicity(One))
import Language.Haskell.TH
import Language.Haskell.TH.Syntax (Lift(..))
import Language.Haskell.TH.Lift ()  -- for Lift Name
import qualified Prelude.Linear as PL
import Prelude.Linear (Ur(..))

import Control.Monad.IO.Class
-- import Debug.Trace

import qualified Data.Array.Growable as GA
import Data.Array.Growable (GrowArray)


type QuoteFail m = (Quote m, MonadFail m)


-- Dt[Double] = (Double, (Int, Contrib))
-- Dt[()] = ()
-- Dt[(a, b)] = (Dt[a], Dt[b])
-- Dt[a -> b] = a -> Int -> (Dt[b], Int)
-- Dt[Int] = Int
-- Dt[Newtype a] = Newtype (Dt[a])
--
-- Dt[eps] = eps
-- Dt[Γ, x : a] = Dt[Γ], x : Dt[a]
--
-- Γ |- i : Int
-- Γ |- t : a
-- ~> Dt[Γ] |- D[i, t] : (Dt[a], Int)
-- D[i, r] = ((r, (i, Contrib [])), i + 1)
-- D[i, x] = (x, i)
-- D[i, ()] = ((), i)
-- D[i, (s, t)] = let (x, i1) = D[i, s]
--                    (y, i2) = D[i1, t]
--                in ((x, y), i2)
-- D[i, s t] = let (f, i1) = D[i, s]
--                 (a, i2) = D[i1, t]
--             in f a i2
-- D[i, \x -> t] = (\x i1 -> D[i1, t], i)
-- D[i, let x = s in t] = let (x, i1) = D[i, s]
--                        in D[i1, t]
-- D[i, op t1..tn] =
--   let ((x1, (di1, cb1)), i1) = D[i, t1]
--       ((x2, (di2, cb2)), i2) = D[i1, t1]
--       ...
--       ((xn, (din, cbn)), in) = D[i{n-1}, tn]
--   in ((op x1..xn
--       ,(in, Contrib [(di1, cb1, dop_1 x1..xn), ..., (din, cbn, dop_n x1..xn)]))
--      ,in + 1)

type BuildState = GrowArray (Contrib, Double)
newtype Contrib = Contrib [(Int, Contrib, Double)]

resolve :: BuildState %1-> BuildState
resolve = \arr ->
  GA.size arr PL.& \(Ur n, arr1) ->
    loop (n - 1) arr1
  where
    loop :: Int -> BuildState %1-> BuildState
    loop 0 arr = arr
    loop i arr =
      GA.get i arr PL.& \(Ur (cb, adj), arr1) ->
        loop (i - 1) (apply cb adj arr1)

    apply :: Contrib -> Double -> BuildState %1-> BuildState
    apply (Contrib []) _ arr = arr
    apply (Contrib ((i, cb, d) : cbs)) a arr =
      GA.get i arr PL.& \(Ur (_, acc), arr1) ->
      GA.set i (cb, acc + a * d) arr1 PL.& \arr2 ->
        apply (Contrib cbs) a arr2

addContrib :: Int -> Contrib -> Double -> BuildState %1-> BuildState
addContrib i cb adj arr =
  GA.get i arr PL.& \(Ur (_, acc), arr1) ->
    GA.set i (cb, acc + adj) arr1


data Structure' tag
  = SDiscrete
  | SScalar  -- Double
  | STuple [Structure' tag]
  | SList (Structure' tag)
  | -- | Instantiation of a newtype, with type arguments inlined.
    SNewtype Name -- ^ data constructor name
             (Structure' tag)
  | -- | Instantiation of a data type, with type arguments inlined.
    SData [(Name, [Structure' tag])]
  | STag !tag
  deriving (Show)

type Structure = Structure' Void

deriveStructureT :: Q Type -> Q Structure
deriveStructureT ty = ty >>= deriveStructure mempty

knownStructure :: KnownType a => Proxy a -> Q Structure
knownStructure = deriveStructure mempty . knownType

deriveStructure :: Map Name (Structure' tag) -> Type -> Q (Structure' tag)
deriveStructure = \env -> go env True
  where
    go :: Map Name (Structure' tag) -> Bool -> Type -> Q (Structure' tag)
    go env scalarsAllowed = \case
      t@AppT{} -> do
        (headty, argtys) <- collectApps t
        argstrucs <- mapM (go env scalarsAllowed) argtys
        goApplied env scalarsAllowed headty argstrucs
      SigT t _ -> go env scalarsAllowed t
      ConT n
        | n `elem` [''Int, ''Int8, ''Int16, ''Int32, ''Int64
                   ,''Word, ''Word8, ''Word16, ''Word32, ''Word64]
        -> return SDiscrete
        | n == ''Double
        -> if scalarsAllowed
             then return SScalar
             else fail "No literal Double scalars allowed in data type used in reverse AD; replace them with a type parameter."
        | otherwise
        -> goApplied env scalarsAllowed (ConT n) []
      ParensT t -> go env scalarsAllowed t
      TupleT 0 -> return (STuple [])
      -- ForallT _ [] t -> go env scalarsAllowed t
      VarT name ->
        case Map.lookup name env of
          Just struc -> return struc
          Nothing -> fail $ "Type variable out of scope: " ++ show name
      -- t@(ForallT _ (_:_) _) -> fail $ "Contexts in foralls not supported in type: " ++ replace '\n' ' ' (pprint t)
      t -> fail $ "Unsupported type in data type: " ++ pprint t

    goApplied :: Map Name (Structure' tag) -> Bool -> Type -> [Structure' tag] -> Q (Structure' tag)
    goApplied env scalarsAllowed headty argstrucs = case headty of
      TupleT n
        | length argstrucs == n
        -> return (STuple argstrucs)

      ListT
        | [struc] <- argstrucs
        -> return (SList struc)

      ConT tyname -> do
        typedecl <- reify tyname >>= \case
          TyConI decl -> return decl
          info -> fail $ "Name " ++ show tyname ++ " is not a type name: " ++ show info
        case typedecl of
          NewtypeD [] _ (map tvbName -> tyvars) _ constr _ -> do
            when (length tyvars /= length argstrucs) $
              fail $ "Type not fully applied: " ++ show headty
            let env' = Map.fromList (zip tyvars argstrucs) <> env
            case constr of
              NormalC conname [(_, fieldty)] -> SNewtype conname <$> go env' scalarsAllowed fieldty
              RecC conname [(_, _, fieldty)] -> SNewtype conname <$> go env' scalarsAllowed fieldty
              _ -> fail $ "Unsupported constructor format on newtype: " ++ show constr
          DataD [] _ (map tvbName -> tyvars) _ constrs [] -> do
            when (length tyvars /= length argstrucs) $
              fail $ "Type not fully applied: " ++ show headty
            let env' = Map.fromList (zip tyvars argstrucs) <> env
                goConstr = \case
                  NormalC conname (map (\(  _,ty) -> ty) -> fieldtys) ->
                    (conname,) <$> mapM (go env' False) fieldtys
                  RecC    conname (map (\(_,_,ty) -> ty) -> fieldtys) ->
                    (conname,) <$> mapM (go env' False) fieldtys
                  constr -> fail $ "Unsupported constructor format on newtype: " ++ show constr
            SData <$> mapM goConstr constrs
          _ -> fail $ "Type not supported: " ++ show tyname

      _ -> fail $ "Type unsupported in data in reverse AD: " ++ show headty

    collectApps :: Type -> Q (Type, [Type])
    collectApps (AppT t1 t2) = do (n, ts) <- collectApps t1
                                  return (n, ts ++ [t2])
    collectApps t = return (t, [])

    tvbName :: TyVarBndr () -> Name
    tvbName (PlainTV n _) = n
    tvbName (KindedTV n _ _) = n

-- | Pattern match on the given data constructor and extract the single value.
unNewtype :: Quote m => Name -> Exp -> m Exp
unNewtype conname expr = do
  name <- newName "x"
  return $ CaseE expr [Match (ConP conname [] [VarP name]) (NormalB (VarE name)) []]

class KnownType a where knownType :: Proxy a -> Type

instance KnownType Int where knownType _ = ConT ''Int
instance KnownType Int8 where knownType _ = ConT ''Int8
instance KnownType Int16 where knownType _ = ConT ''Int16
instance KnownType Int32 where knownType _ = ConT ''Int32
instance KnownType Int64 where knownType _ = ConT ''Int64
instance KnownType Word where knownType _ = ConT ''Word
instance KnownType Word8 where knownType _ = ConT ''Word8
instance KnownType Word16 where knownType _ = ConT ''Word16
instance KnownType Word32 where knownType _ = ConT ''Word32
instance KnownType Word64 where knownType _ = ConT ''Word64
instance KnownType () where knownType _ = TupleT 0
instance TypeError ('Text "Only Double is an active type for now (Float isn't)") => KnownType Float where knownType = undefined
instance KnownType Double where knownType _ = ConT ''Double

instance (KnownType a, KnownType b) => KnownType (a, b) where
  knownType _ = TupleT 2 `AppT` knownType (Proxy @a) `AppT` knownType (Proxy @b)
instance (KnownType a, KnownType b, KnownType c) => KnownType (a, b, c) where
  knownType _ = TupleT 3 `AppT` knownType (Proxy @a) `AppT` knownType (Proxy @b) `AppT` knownType (Proxy @c)
instance (KnownType a, KnownType b, KnownType c, KnownType d) => KnownType (a, b, c, d) where
  knownType _ = TupleT 3 `AppT` knownType (Proxy @a) `AppT` knownType (Proxy @b) `AppT` knownType (Proxy @c) `AppT` knownType (Proxy @d)

instance KnownType a => KnownType [a] where
  knownType _ = ListT `AppT` knownType (Proxy @a)

-- | Use on the top level for a newtype that you wish to use in 'reverseAD'.
-- For example:
--
--     {-# LANGUAGE FlexibleContexts, TemplateHaskell, UndecidableInstances #-}
--     import Data.Monoid (Sum(..))
--     useTypeForReverseAD ''Sum
--
-- Note that, due to the GHC stage restriction, you cannot put the
-- 'useTypeForReverseAD' invocation and the usage of the datatype in a
-- 'reverseAD' splice in the same file. Put the 'useTypeForReverseAD'
-- invocation in a different module and import that.
-- useTypeForReverseAD :: Name -> Q [Dec]
-- useTypeForReverseAD tyname = do
--   typedecl <- reify tyname >>= \case
--     TyConI decl -> return decl
--     info -> fail $ "Name " ++ show tyname ++ " is not a type name: " ++ show info
--   (conname, tyvars, fieldty) <- case typedecl of
--     NewtypeD [] _ tyvars _ constr _ -> case constr of
--       NormalC conname [(_, fieldty)] -> return (conname, map tvbName tyvars, fieldty)
--       RecC conname [(_, _, fieldty)] -> return (conname, map tvbName tyvars, fieldty)
--       _ -> fail $ "Unsupported constructor format on newtype: " ++ show constr
--     _ -> fail "Only newtypes supported for now"
--   checkNoScalars fieldty
--   connameexp <- lift conname
--   buildname <- newName "build"
--   let builddecs =
--         [SigD buildname (ArrowT `AppT` (ConT ''Structure `AppT` fieldty)
--                                 `AppT` (ConT ''Structure
--                                           `AppT` foldl AppT (ConT tyname) (map VarT tyvars)))
--         ,ValD (VarP buildname)
--               (NormalB (ConE 'SNewtype `AppE` connameexp))
--               []]
--   return [InstanceD Nothing
--                     [ConT ''KnownStructure `AppT` fieldty]
--                     (ConT ''KnownStructure
--                        `AppT` foldl AppT (ConT tyname) (map VarT tyvars))
--                     [ValD (VarP 'knownStructure)
--                           (NormalB (LetE builddecs
--                                          (AppE (VarE buildname) (VarE 'knownStructure))))
--                           []]]
--   where
--     tvbName :: TyVarBndr () -> Name
--     tvbName (PlainTV n _) = n
--     tvbName (KindedTV n _ _) = n

--     checkNoScalars :: MonadFail m => Type -> m ()
--     checkNoScalars (ForallT _ [] t) = checkNoScalars t
--     checkNoScalars (AppT t1 t2) = checkNoScalars t1 >> checkNoScalars t2
--     checkNoScalars (SigT t _) = checkNoScalars t
--     checkNoScalars (VarT _) = return ()
--     checkNoScalars (ConT n)
--       | n `elem` [''Int, ''Int8, ''Int16, ''Int32, ''Int64
--                  ,''Word, ''Word8, ''Word16, ''Word32, ''Word64]
--       = return ()
--       | n == ''Double
--       = fail "No literal Double scalars allowed in type used in reverse AD; replace them with a type parameter."
--     checkNoScalars (ParensT t) = checkNoScalars t
--     checkNoScalars (TupleT _) = return ()
--     checkNoScalars ArrowT = return ()
--     checkNoScalars MulArrowT = return ()
--     checkNoScalars ListT = return ()
--     checkNoScalars t@(ForallT _ (_:_) _) = fail $ "Contexts in foralls not supported in type: " ++ replace '\n' ' ' (pprint t)
--     checkNoScalars t = fail $ "Unsupported type in data type: " ++ replace '\n' ' ' (pprint t)

--     replace :: (Eq a, Functor f) => a -> a -> f a -> f a
--     replace from to = fmap (\x -> if x == from then to else x)


-- | Use as follows:
--
--     > :t $$(reverseAD @_ @Double [|| \(x, y) -> x * y ||])
--     (Double, Double) -> (Double, Double -> (Double, Double))
reverseAD :: forall a b. (KnownType a, KnownType b)
          => Code Q (a -> b)
          -> Code Q (a -> (b, b -> a))
reverseAD = reverseAD' (knownStructure (Proxy @a)) (knownStructure (Proxy @b))

-- | Same as 'reverseAD', but with user-supplied 'Structure's.
reverseAD' :: forall a b.
              Q Structure  -- ^ a
           -> Q Structure  -- ^ b
           -> Code Q (a -> b)
           -> Code Q (a -> (b, b -> a))
reverseAD' inpStruc outStruc (unTypeCode -> inputCode) =
  unsafeCodeCoerce $ do
    inpStruc' <- inpStruc
    outStruc' <- outStruc
    ex <- inputCode
    transform inpStruc' outStruc' ex

transform :: Structure -> Structure -> Exp -> Q Exp
transform inpStruc outStruc (LamE [pat] expr) = do
  argvar <- newName "arg"
  onevar <- newName "one"
  inp <- numberInput inpStruc (VarE argvar) onevar
  idvar <- newName "i0"
  patbound <- boundVars pat
  ddrexpr <- ddr patbound idvar expr
  deinterexpr <- deinterleave outStruc (AppE (VarE 'fst) ddrexpr)
  primalname <- newName "primal"
  dualname <- newName "dual"
  adjname <- newName "adjoint"
  stagedvecname <- newName "stagedvec"
  vecname <- newName "vec"
  let composeLinearFuns :: [Exp] -> Exp
      composeLinearFuns [] = VarE 'PL.id
      composeLinearFuns l = foldl1 (\a b -> InfixE (Just a) (VarE '(PL..)) (Just b)) l
  (reconstructExp', _) <- reconstruct inpStruc (VarE argvar) (VarE vecname) onevar
  let reconstructExp = AppE (VarE 'fst) reconstructExp'
  return (LamE [VarP argvar] $
            LetE [ValD (VarP onevar) (NormalB (SigE (LitE (IntegerL 1)) (ConT ''Int))) []
                 ,ValD (TupP [pat, VarP idvar]) (NormalB inp) []
                 ,ValD (TupP [VarP primalname, VarP dualname]) (NormalB deinterexpr) []] $
              pair (VarE primalname)
                   (LamE [VarP adjname] $
                      LetE [ValD (ConP 'Ur [] [VarP stagedvecname])
                                 (NormalB
                                    (foldl AppE (VarE 'GA.alloc)
                                                [LitE (IntegerL 0)
                                                ,pair (AppE (ConE 'Contrib) (ListE []))
                                                      (LitE (RationalL 0.0))
                                                ,composeLinearFuns
                                                   [VarE 'GA.freeze
                                                   ,VarE 'resolve
                                                   ,AppE (VarE dualname) (VarE adjname)]]))
                                 []
                           ,ValD (VarP vecname)
                                 (NormalB (VarE 'V.map `AppE` VarE 'snd `AppE` VarE stagedvecname))
                                 []]
                        reconstructExp))
transform inpStruc outStruc (LamE [] body) =
  transform inpStruc outStruc body
transform inpStruc outStruc (LamE (pat : pats) body) =
  transform inpStruc outStruc (LamE [pat] (LamE pats body))
transform _ _ expr =
  fail $ "Top-level expression in reverseAD must be lambda, but is: " ++ show expr

composeL :: [a %1-> a] -> a %1-> a
composeL [] = PL.id
composeL [f] = f
composeL (f:fs) = f PL.. composeL fs

deinterleaveList :: (da -> (a, a -> BuildState %1-> BuildState))
                 -> [da] -> ([a], [a] -> BuildState %1-> BuildState)
deinterleaveList f l =
  let (l', funs) = unzip (map f l)
  in (l', \adjs -> composeL (zipWith ($) funs adjs))

-- outexp :: Dt[a]                            -- expression returning the output of the transformed program
-- result :: (a                               -- primal result
--           ,a -> BuildState -o BuildState)  -- given adjoint, add initial contributions
deinterleave :: Quote m => Structure -> Exp -> m Exp
deinterleave topstruc outexp = case topstruc of
  SDiscrete -> return (pair outexp (LamE [WildP] (VarE 'PL.id)))

  SScalar -> do
    -- outexp :: (Double, (Int, Contrib))
    -- adjexp :: Double
    primalname <- newName "prim"
    idname <- newName "id"
    cbname <- newName "cb"
    return $
      LetE [ValD (TupP [VarP primalname, TupP [VarP idname, VarP cbname]]) (NormalB outexp) []] $
        pair (VarE primalname)
             (VarE 'addContrib `AppE` VarE idname `AppE` VarE cbname)  -- partially-applied

  STuple strucs -> do
    (funs, outnames, adjnames) <- fmap unzip3 . forM (zip strucs [1::Int ..]) $ \(struc', index) -> do
      outn <- newName ("out" ++ show index)
      adjn <- newName ("adj" ++ show index)
      fun <- deinterleave struc' (VarE outn)
      return (fun, outn, adjn)
    fulloutname <- newName "out"
    case strucs of
      [] -> return (pair (TupE []) (LamE [WildP] (VarE 'PL.id)))
      _ -> return $
        LetE [ValD (AsP fulloutname (TupP (map VarP outnames))) (NormalB outexp) []] $
          pair (VarE fulloutname)
               (LamE [TupP (map VarP adjnames)] $
                  foldr1 (\e1 e2 -> VarE '(PL..) `AppE` e1 `AppE` e2)
                         (zipWith AppE funs (map VarE adjnames)))

  SList struc -> do
    argvar <- newName "x"
    body <- deinterleave struc (VarE argvar)
    return $ VarE 'deinterleaveList
              `AppE` LamE [VarP argvar] body
              `AppE` outexp

  SNewtype conname struc -> do
    outexp' <- unNewtype conname outexp  -- strip off the newtype wrapper first
    expr <- deinterleave struc outexp'
    primalname <- newName "primal"
    dualname <- newName "dualf"
    return $ CaseE expr
      [Match (TupP [VarP primalname, VarP dualname])
             (NormalB (pair (ConE conname `AppE` VarE primalname)
                            (InfixE (Just (VarE dualname)) (VarE '(.)) (Just (ConE conname)))))
             []]

  SData [] ->
    return $ CaseE outexp []

  SData datacons -> do
    let maxlen = maximum [length fieldstrucs | (_, fieldstrucs) <- datacons]
    allvars <- mapM (\i -> newName ("x" ++ show i)) [1 .. maxlen]
    matches <- sequence
      [do let vars = take (length fieldstrucs) allvars
          exprs <- zipWithM deinterleave fieldstrucs (map VarE vars)
          return $ Match (ConP conname [] (map VarP vars))
                         (NormalB (foldl AppE (ConE conname) exprs))
                         []
      | (conname, fieldstrucs) <- datacons]
    return $ CaseE outexp matches

reconstructList :: (Int -> s -> (s, Int)) -> [s] -> Int -> ([s], Int)
reconstructList f primal i0 = swap (mapAccumL (\i x -> swap (f i x)) i0 primal)

-- struc :: Structure s                -- input structure
-- inexp :: s                          -- primal input (duplicable)
-- vecexp :: Vector (Contrib, Double)  -- resolved input adjoint vector (duplicable)
-- startid :: Name Int                 -- first ID in this substructure
-- ~> result :: (s, Int)               -- final input adjoint plus next ID after this substructure
-- In ID generation monad; also returns whether the inexp argument was actually used
reconstruct :: Quote m => Structure -> Exp -> Exp -> Name -> m (Exp, Bool)
reconstruct topstruc inexp vecexp startid = case topstruc of
  SDiscrete -> return (pair inexp (VarE startid), True)

  SScalar -> return (pair (InfixE (Just vecexp) (VarE '(V.!)) (Just (VarE startid)))
                          (AppE (VarE 'succ) (VarE startid))
                    ,False)

  STuple strucs -> do
    innames <- zipWithM (\_ i -> newName ("in" ++ show i)) strucs [1::Int ..]
    recnames <- zipWithM (\_ i -> newName ("y" ++ show i)) strucs [1::Int ..]
    idnames <- zipWithM (\_ i -> newName ("i" ++ show i)) strucs [1::Int ..]
    (recexps, useds) <-
      unzip <$> zipWithM3 (\str inn idn -> reconstruct str inn vecexp idn)
                          strucs (map VarE innames) (startid : idnames)
    let outid = case strucs of [] -> startid ; _ -> last idnames
    return $
      (LetE ((if or useds
                then [ValD (TupP (zipWith (\n u -> if u then VarP n else WildP)
                                          innames useds))
                           (NormalB inexp) []]
                else [])
             ++ [ValD (TupP [VarP recname, VarP idname]) (NormalB recexp) []
                | (recname, idname, recexp) <- zip3 recnames idnames recexps]) $
         pair (TupE (map (Just . VarE) recnames))
              (VarE outid)
      ,or useds)

  SList struc -> do
    argvar <- newName "x"
    idvar <- newName "i"
    (body, used) <- reconstruct struc (VarE argvar) vecexp idvar
    return (VarE 'reconstructList
              `AppE` LamE [VarP idvar, if used then VarP argvar else WildP] body
              `AppE` inexp
              `AppE` VarE startid
           ,True)

  SNewtype conname struc -> do
    inexp' <- unNewtype conname inexp  -- strip off the newtype wrapper first
    (expr, used) <- reconstruct struc inexp' vecexp startid
    return (VarE 'first `AppE` ConE conname `AppE` expr
           ,used)

-- Set of names bound in the program at this point
type Env = Set Name

-- Γ |- i : Int                        -- idName
-- Γ |- t : a                          -- expression
-- ~> Dt[Γ] |- D[i, t] : (Dt[a], Int)  -- result
ddr :: Env -> Name -> Exp -> Q Exp
ddr env idName = \case
  VarE name
    | name `Set.member` env -> return (pair (VarE name) (VarE idName))
    | name == 'negate -> do
        xname <- newName "x"
        iname <- newName "i"
        let function = LamE [VarP xname, VarP iname] $
              foldl AppE (VarE 'applyUnaryOp)
                [VarE xname
                ,VarE 'negate
                ,LamE [WildP] (LitE (IntegerL (-1)))
                ,VarE iname]
        return (pair function (VarE idName))
    | otherwise -> fail $ "Free variables not supported in reverseAD: " ++ show name ++ " (env = " ++ show env ++ ")"

  ConE name
    | name `elem` ['[]] -> return (pair (ConE name) (VarE idName))
    | otherwise -> fail $ "Data constructor not supported in reverseAD: " ++ show name

  LitE lit -> case lit of
    RationalL _ -> return (pair (pair (LitE lit)
                                      (pair (VarE idName) (AppE (ConE 'Contrib) (ListE []))))
                                (InfixE (Just (VarE idName))
                                        (VarE '(+))
                                        (Just (LitE (IntegerL 1)))))
    FloatPrimL _ -> fail "float prim?"
    DoublePrimL _ -> fail "double prim?"
    IntegerL _ -> return (pair (LitE lit) (VarE idName))
    _ -> fail $ "literal? " ++ show lit

  AppE e1 e2 -> do
    (letwrap, [funname, argname], outid) <- ddrList env [e1, e2] idName
    return (letwrap (VarE funname `AppE` VarE argname `AppE` VarE outid))

  InfixE (Just e1) (VarE opname) (Just e2) -> do
    let handleNum =
          let num = LitE . IntegerL in
          if | opname == '(+) -> Just ((False, False), \_ _ -> pair (num 1) (num 1))
             | opname == '(-) -> Just ((False, False), \_ _ -> pair (num 1) (num (-1)))
             | opname == '(*) -> Just ((True, True), \x y -> pair y x)
             | otherwise -> Nothing
            & \case
              Nothing -> Nothing
              Just ((gxused, gyused), gradientfun) -> Just $ do
                (letwrap, [x1name, x2name], outid) <- ddrList env [e1, e2] idName
                t1name <- newName "arg1"
                t2name <- newName "arg2"
                return $ letwrap $
                  foldl AppE (VarE 'applyBinaryOp)
                    [VarE x1name, VarE x2name
                    ,VarE opname
                    ,LamE [if gxused then VarP t1name else WildP
                          ,if gyused then VarP t2name else WildP] $
                       gradientfun (VarE t1name) (VarE t2name)
                    ,VarE outid]

        handleOrd =
          if opname `elem` ['(==), '(/=), '(<), '(>), '(<=), '(>=)]
            then Just $ do
              (letwrap, [x1name, x2name], outid) <- ddrList env [e1, e2] idName
              t1name <- newName "arg1"
              t2name <- newName "arg2"
              return $ letwrap $
                pair (foldl AppE (VarE 'applyCmpOp)
                        [VarE x1name, VarE x2name
                        ,LamE [VarP t1name, VarP t2name] $
                           InfixE (Just (VarE t1name)) (VarE opname) (Just (VarE t2name))])
                     (VarE outid)
            else Nothing

    case asum [handleNum, handleOrd] of
      Nothing -> fail ("Unsupported infix operator " ++ show opname)
      Just act -> act

  InfixE (Just e1) (ConE constr) (Just e2)
    | constr == '(:) -> do
        (letwrap, [xname, xsname], outid) <- ddrList env [e1, e2] idName
        return $ letwrap $
          pair (InfixE (Just (VarE xname)) (ConE '(:)) (Just (VarE xsname)))
               (VarE outid)
    | otherwise -> fail $ "Unsupported infix operator: " ++ show constr

  e@InfixE{} -> fail $ "Unsupported operator section: " ++ show e

  ParensE e -> ParensE <$> ddr env idName e

  LamE [pat] e -> do
    idName1 <- newName "i"
    patbound <- boundVars pat
    e' <- ddr (env <> patbound) idName1 e
    return (pair (LamE [pat, VarP idName1] e') (VarE idName))

  TupE mes
    | Just es <- sequence mes -> do
        (letwrap, vars, outid) <- ddrList env es idName
        return (letwrap (pair (TupE (map (Just . VarE) vars))
                              (VarE outid)))
    | otherwise -> notSupported "Tuple sections" (Just (show (TupE mes)))

  CondE e1 e2 e3 -> do
    e1' <- ddr env idName e1
    boolName <- newName "bool"
    idName1 <- newName "i1"
    e2' <- ddr env idName1 e2
    e3' <- ddr env idName1 e3
    return (LetE [ValD (TupP [VarP boolName, VarP idName1]) (NormalB e1') []]
              (CondE (VarE boolName) e2' e3'))

  LetE decs body -> do
    decs' <- mapM desugarDec decs
    checkDecsNonRecursive decs' >>= \case
      Just (map fst3 -> declared) -> do
        (decs'', idName') <- transDecs (env <> Set.fromList declared) decs' idName
        body' <- ddr (env <> Set.fromList declared) idName' body
        return (LetE decs'' body')
      Nothing -> notSupported "Recursive or non-variable let-bindings" (Just (show (LetE decs' body)))

  CaseE expr matches -> do
    (letwrap, [evar], outid) <- ddrList env [expr] idName
    matches' <- sequence
      [case mat of
         Match pat (NormalB rhs) [] -> do
           patbound <- boundVars pat
           pat' <- ddrPat pat
           rhs' <- ddr (env <> patbound) outid rhs
           return (pat', rhs')
         _ -> fail "Where blocks or guards not supported in case expressions"
      | mat <- matches]
    return $ letwrap $
      CaseE (VarE evar)
        [Match pat (NormalB rhs) [] | (pat, rhs) <- matches']

  ListE es -> do
    (letwrap, vars, outid) <- ddrList env es idName
    return (letwrap (pair (ListE (map VarE vars))
                          (VarE outid)))

  UnboundVarE n -> fail $ "Free variable in reverseAD: " ++ show n

  -- Constructs that we can express in terms of other, simpler constructs handled above
  LamE [] e -> ddr env idName e  -- is this even a valid AST?
  LamE (pat : pats@(_:_)) e -> ddr env idName (LamE [pat] (LamE pats e))
  LamCaseE mats -> do
    name <- newName "lcarg"
    ddr env idName (LamE [VarP name] (CaseE (VarE name) mats))

  -- Unsupported constructs
  e@AppTypeE{} -> notSupported "Type applications" (Just (show e))
  e@UInfixE{} -> notSupported "UInfixE" (Just (show e))
  e@UnboxedTupE{} -> notSupported "Unboxed tuples" (Just (show e))
  e@UnboxedSumE{} -> notSupported "Unboxed sums" (Just (show e))
  e@MultiIfE{} -> notSupported "Multi-way ifs" (Just (show e))
  e@DoE{} -> notSupported "Do blocks" (Just (show e))
  e@MDoE{} -> notSupported "MDo blocks" (Just (show e))
  e@CompE{} -> notSupported "List comprehensions" (Just (show e))
  e@ArithSeqE{} -> notSupported "Arithmetic sequences" (Just (show e))
  e@SigE{} -> fail $ "Type ascriptions not supported, because I'm lazy and then I need to write code to rewrite types (" ++ show e ++ ")"
  e@RecConE{} -> notSupported "Records" (Just (show e))
  e@RecUpdE{} -> notSupported "Records" (Just (show e))
  e@StaticE{} -> notSupported "Cloud Haskell" (Just (show e))
  e@LabelE{} -> notSupported "Overloaded labels" (Just (show e))
  e@ImplicitParamVarE{} -> notSupported "Implicit parameters" (Just (show e))
  e@GetFieldE{} -> notSupported "Records" (Just (show e))
  e@ProjectionE{} -> notSupported "Records" (Just (show e))

pair :: Exp -> Exp -> Exp
pair e1 e2 = TupE [Just e1, Just e2]

-- | Given list of expressions and the input ID, returns a let-wrapper that
-- defines a variable for each item in the list (differentiated), the names of
-- those variables, and the output ID name (in scope in the let-wrapper).
-- The expressions must all have the same, given, environment.
ddrList :: Env -> [Exp] -> Name -> Q (Exp -> Exp, [Name], Name)
ddrList env es idName = do
  -- output varnames of the expressions
  names <- mapM (\idx -> (,) <$> newName ("x" ++ show idx) <*> newName ("i" ++ show idx))
                (take (length es) [1::Int ..])
  -- the let-binding pairs
  binds <- zipWithM3 (\ni_in (nx, ni_out) e -> do e' <- ddr env ni_in e
                                                  return ((nx, ni_out), e'))
                     (idName : map snd names) names es
  let out_index = case names of
                    [] -> idName
                    l -> snd (last l)
  return (LetE [ValD (TupP [VarP nx, VarP ni]) (NormalB e) []
               | ((nx, ni), e) <- binds]
         ,map fst names
         ,out_index)

ddrPat :: Pat -> Q Pat
ddrPat = \case
  LitP{} -> fail "Literals in patterns unsupported"
  p@VarP{} -> return p
  TupP ps -> TupP <$> traverse ddrPat ps
  UnboxedTupP ps -> UnboxedTupP <$> traverse ddrPat ps
  p@UnboxedSumP{} -> notSupported "Unboxed sums" (Just (show p))
  p@(ConP name tyapps args)
    | not (null tyapps) -> notSupported "Type applications in patterns" (Just (show p))
    | name `elem` ['(:), '[]] -> ConP name [] <$> traverse ddrPat args
    | otherwise -> do
        conty <- reifyType name
        appliedType <- case typeApplyN conty (length args) of
          Just ty -> return ty
          Nothing -> fail $ show (length args) ++ " arguments given to " ++ show conty ++ " but not a function type"
        tyargs <- case extractTypeCon appliedType of
                    Just (_, tyargs)
                      | Just tyargs' <- traverse (\case VarT n -> Just n
                                                        _ -> Nothing)
                                                 tyargs
                      -> return tyargs'
                      | otherwise
                      -> fail "Normal constructor has GADT properties?"
                    Nothing -> fail $ "Unknown type format " ++ show appliedType
        -- liftIO (print appliedType)
        -- liftIO (print tyargs)
        -- The fact that 'deriveStructure' returns successfully implies that the type is fine
        _ <- deriveStructure (Map.fromList (zip tyargs (repeat (STag ())))) appliedType
        ConP name [] <$> traverse ddrPat args
        -- typename <- case extractTypeCon appliedType of
        --   Just ty -> return ty
        --   Nothing -> fail $ "Unknown type format " ++ show appliedType
        -- typedecl <- reify typename >>= \case
        --   TyConI decl -> return decl
        --   info -> fail $ "Constructor of " ++ show name ++ " used in pattern, but not a type? " ++ show info
        -- if checkStructuralType typedecl
        --   then ConP name [] <$> traverse ddrPat args
        --   else notSupported "Pattern matching on this type" (Just (show typename))
  InfixP p1 name p2
    | name == '(:) -> InfixP <$> ddrPat p1 <*> return name <*> ddrPat p2
    | otherwise -> notSupported "This constructor in a pattern" (Just (show name))
  p@UInfixP{} -> notSupported "UInfix patterns" (Just (show p))
  ParensP p -> ParensP <$> ddrPat p
  p@TildeP{} -> notSupported "Irrefutable patterns" (Just (show p))
  p@BangP{} -> notSupported "Bang patterns" (Just (show p))
  AsP name p -> AsP name <$> ddrPat p
  WildP -> return WildP
  p@RecP{} -> notSupported "Records" (Just (show p))
  ListP ps -> ListP <$> traverse ddrPat ps
  p@SigP{} -> notSupported "Type signatures in patterns, because then I need to rewrite types and I'm lazy" (Just (show p))
  p@ViewP{} -> notSupported "View patterns" (Just (show p))

typeApplyN :: Type -> Int -> Maybe Type
typeApplyN t 0 = Just t
typeApplyN (ForallT _ _ t) n = typeApplyN t n
typeApplyN (ArrowT `AppT` _ `AppT` t) n = typeApplyN t (n - 1)
typeApplyN (MulArrowT `AppT` PromotedT multi `AppT` _ `AppT` t) n
  | multi == 'One = typeApplyN t (n - 1)
typeApplyN _ _ = Nothing

extractTypeCon :: Type -> Maybe (Name, [Type])
extractTypeCon (AppT t arg) = second (++ [arg]) <$> extractTypeCon t
extractTypeCon (ConT n) = Just (n, [])
extractTypeCon _ = Nothing

-- -- | Checks that the type with this declaration is isomorphic to nested
-- -- products/sums plus possibly some discrete literal types. This is a
-- -- sufficient criterion for the constructors of the type being allowable in
-- -- expressions and patterns under 'reverseAD'.
-- checkStructuralType :: Dec -> Bool
-- checkStructuralType = \case
--   NewtypeD [] _ _ _ constr _ -> goCon constr
--   DataD [] _ _ _ constrs _ -> all goCon constrs
--   _ -> False
--   where
--     goCon :: Con -> Bool
--     goCon = \case
--       NormalC _ tys -> all goField [ty | (_, ty) <- tys]
--       RecC _ tys -> all goField [ty | (_, _, ty) <- tys]
--       _ -> False

--     goField :: Type -> Bool
--     goField (VarT _) = True
--     goField _ = False

class NumOperation a where
  type DualNum a = r | r -> a
  applyBinaryOp
    :: DualNum a -> DualNum a  -- arguments
    -> (a -> a -> a)           -- primal
    -> (a -> a -> (a, a))      -- gradient given inputs (assuming adjoint 1)
    -> Int                     -- nextid
    -> (DualNum a, Int)        -- output and nextid
  applyUnaryOp
    :: DualNum a               -- argument
    -> (a -> a)                -- primal
    -> (a -> a)                -- derivative given input (assuming adjoint 1)
    -> Int                     -- nextid
    -> (DualNum a, Int)        -- output and nextid
  applyCmpOp
    :: DualNum a -> DualNum a  -- arguments
    -> (a -> a -> Bool)        -- primal
    -> Bool                    -- output

instance NumOperation Double where
  type DualNum Double = (Double, (Int, Contrib))
  applyBinaryOp (x, (xi, xcb)) (y, (yi, ycb)) primal grad nextid =
    let (dx, dy) = grad x y
    in ((primal x y
        ,(nextid
         ,Contrib [(xi, xcb, dx), (yi, ycb, dy)]))
       ,nextid + 1)
  applyUnaryOp (x, (xi, xcb)) primal grad nextid =
    ((primal x, (nextid, Contrib [(xi, xcb, grad x)])), nextid + 1)
  applyCmpOp (x, _) (y, _) f = f x y

instance NumOperation Int where
  type DualNum Int = Int
  applyBinaryOp x y primal _ nextid = (primal x y, nextid)
  applyUnaryOp x primal _ nextid = (primal x, nextid)
  applyCmpOp x y f = f x y

desugarDec :: QuoteFail m => Dec -> m Dec
desugarDec = \case
  dec@(ValD (VarP _) (NormalB _) []) -> return $ dec

  FunD _ [] -> fail "Function declaration with empty list of clauses?"

  FunD name clauses
    | not (allEqual [length pats | Clause pats _ _ <- clauses])
    -> fail "Clauses of a function declaration do not all have the same number of arguments"
    | not (and [null decs | Clause _ _ decs <- clauses])
    -> fail $ "Where blocks not supported in declaration of " ++ show name
    | length [() | Clause _ (NormalB _) _ <- clauses] /= length clauses
    -> fail $ "Guards not supported in declaration of " ++ show name
    | otherwise
    -> do
      let nargs = head [length pats | Clause pats _ _ <- clauses]
      argnames <- mapM (\i -> newName ("arg" ++ show i)) [1..nargs]
      let body = LamE (map VarP argnames) $
                   CaseE (TupE (map (Just . VarE) argnames))
                     [Match (TupP ps) (NormalB rhs) []
                     | Clause ps ~(NormalB rhs) ~[] <- clauses]
      return $ ValD (VarP name) (NormalB body) []

  dec -> fail $ "Only simple let bindings supported in reverseAD: " ++ show dec
  where
    allEqual :: Eq a => [a] -> Bool
    allEqual [] = True
    allEqual (x:xs) = all (== x) xs

-- | Differentiate a declaration, given a variable containing the next ID to
-- generate. Modifies the declaration to bind the next ID to a new name, which
-- is returned.
transDec :: Env -> Dec -> Name -> Q (Dec, Name)
transDec env dec idName = case dec of
  ValD (VarP name) (NormalB body) [] -> do
    idName1 <- newName "i"
    body' <- ddr env idName body
    return (ValD (TupP [VarP name, VarP idName1]) (NormalB body') [], idName1)

  _ -> fail $ "How did this declaration get through desugaring? " ++ show dec

-- | `sequence 'transDec'`
transDecs :: Env -> [Dec] -> Name -> Q ([Dec], Name)
transDecs _ [] n = return ([], n)
transDecs env (d : ds) n = do
  (d', n') <- transDec env d n
  (ds', n'') <- transDecs env ds n'
  return (d' : ds', n'')

-- | If these declarations occur in a let block, check that all dependencies go
-- backwards, i.e. it would be valid to replace the let block with a chain of
-- single-dec lets. If non-recursive, returns, for each variable defined: the
-- name, the free variables of its right-hand side, and its right-hand side.
checkDecsNonRecursive :: MonadFail m => [Dec] -> m (Maybe [(Name, Set Name, Exp)])
checkDecsNonRecursive decs = do
  let processDec :: MonadFail m => Dec -> m (Name, Set Name, Exp)
      processDec = \case
        ValD (VarP name) (NormalB e) [] -> (name,,e) <$> freeVars e
        dec -> fail $ "Unsupported declaration in let: " ++ show dec
  tups <- mapM processDec decs
  -- TODO: mild quadratic behaviour with this notElem
  let nonRecursive :: [Name] -> Set Name -> Bool
      nonRecursive boundAfterThis frees = all (\name -> name `notElem` boundAfterThis) (toList frees)
  if all (\((_, frees, rhs), boundAfterThis) ->
            case rhs of LamE (_:_) _ -> True
                        _ -> nonRecursive boundAfterThis frees)
         (zip tups (tail (tails (map fst3 tups))))
    then return (Just tups)
    else return Nothing

numberList :: (Int -> a -> (da, Int)) -> [a] -> Int -> ([da], Int)
numberList f l i0 = swap (mapAccumL (\i x -> swap (f i x)) i0 l)

-- input :: a
-- nextid :: Name Int
-- result :: (Dt[a], Int)
numberInput :: Quote m => Structure -> Exp -> Name -> m Exp
numberInput topstruc input nextid = case topstruc of
  SDiscrete -> return (pair input (VarE nextid))

  SScalar -> return $
    pair (pair input
               (pair (VarE nextid)
                     (ConE 'Contrib `AppE` ListE [])))
         (AppE (VarE 'succ) (VarE nextid))

  STuple strucs -> do
    names <- mapM (const (newName "inp")) strucs
    postnames <- mapM (const (newName "inp'")) strucs
    idnames <- zipWithM (\_ i -> newName ("i" ++ show i)) strucs [1::Int ..]
    let outid = case idnames of [] -> nextid ; _ -> last idnames
    exps <- zipWithM3 (\str -> numberInput str) strucs (map VarE names) (nextid : idnames)
    return (LetE (ValD (TupP (map VarP names)) (NormalB input) []
                 : [ValD (TupP [VarP postname, VarP idname]) (NormalB expr) []
                   | (postname, idname, expr) <- zip3 postnames idnames exps])
                 (pair (TupE (map (Just . VarE) postnames))
                       (VarE outid)))

  SList eltstruc -> do
    idxarg <- newName "i"
    eltarg <- newName "x"
    body <- numberInput eltstruc (VarE eltarg) idxarg
    return $ foldl AppE (VarE 'numberList)
      [LamE [VarP idxarg, VarP eltarg] body
      ,input
      ,VarE nextid]

  SNewtype conname struc -> do
    input' <- unNewtype conname input  -- strip off the newtype wrapper first
    expr <- numberInput struc input' nextid
    return (VarE 'first `AppE` ConE conname `AppE` expr)

fst3 :: (a, b, c) -> a
fst3 (a, _, _) = a

freeVars :: MonadFail m => Exp -> m (Set Name)
freeVars = \case
  VarE n -> return (Set.singleton n)
  ConE{} -> return mempty
  LitE{} -> return mempty
  AppE e1 e2 -> (<>) <$> freeVars e1 <*> freeVars e2
  AppTypeE e1 _ -> freeVars e1
  InfixE me1 e2 me3 -> combine [maybe (return mempty) freeVars me1
                               ,freeVars e2
                               ,maybe (return mempty) freeVars me3]
  e@UInfixE{} -> notSupported "UInfixE" (Just (show e))
  ParensE e -> freeVars e
  LamE pats e -> (Set.\\) <$> freeVars e <*> combine (map boundVars pats)
  LamCaseE mats -> combine [case mat of
                              Match pat (NormalB e) [] -> (Set.\\) <$> freeVars e <*> boundVars pat
                              _ -> fail $ "Unsupported pattern in LambdaCase (neither guards nor where-blocks supported): " ++ show mat
                           | mat <- mats]
  TupE es -> combine (map (maybe (return mempty) freeVars) es)
  UnboxedTupE es -> combine (map (maybe (return mempty) freeVars) es)
  e@UnboxedSumE{} -> notSupported "Unboxed sums" (Just (show e))
  CondE e1 e2 e3 -> combine (map freeVars [e1, e2, e3])
  e@MultiIfE{} -> notSupported "Multi-way ifs" (Just (show e))
  LetE decs body -> do
    checkDecsNonRecursive decs >>= \case
        Just tups -> (Set.\\) <$> freeVars body <*> pure (Set.fromList (map fst3 tups))
        Nothing -> fail $ "Recursive declarations in let unsupported: " ++ show (LetE decs body)
  CaseE e ms -> (<>) <$> freeVars e <*> combine (map go ms)
    where go :: MonadFail m => Match -> m (Set Name)
          go (Match pat (NormalB rhs) []) = (Set.\\) <$> freeVars rhs <*> boundVars pat
          go mat = fail $ "Unsupported match in case: " ++ show mat
  e@DoE{} -> notSupported "Do blocks" (Just (show e))
  e@MDoE{} -> notSupported "MDo blocks" (Just (show e))
  e@CompE{} -> notSupported "List comprehensions" (Just (show e))
  e@ArithSeqE{} -> notSupported "Arithmetic sequences" (Just (show e))
  ListE es -> combine (map freeVars es)
  SigE e _ -> freeVars e
  e@RecConE{} -> notSupported "Records" (Just (show e))
  e@RecUpdE{} -> notSupported "Records" (Just (show e))
  e@StaticE{} -> notSupported "Cloud Haskell" (Just (show e))
  UnboundVarE n -> return (Set.singleton n)
  e@LabelE{} -> notSupported "Overloaded labels" (Just (show e))
  e@ImplicitParamVarE{} -> notSupported "Implicit parameters" (Just (show e))
  e@GetFieldE{} -> notSupported "Records" (Just (show e))
  e@ProjectionE{} -> notSupported "Records" (Just (show e))

boundVars :: MonadFail m => Pat -> m (Set Name)
boundVars = \case
  LitP _ -> return mempty
  VarP n -> return (Set.singleton n)
  TupP ps -> combine (map boundVars ps)
  UnboxedTupP ps -> combine (map boundVars ps)
  p@UnboxedSumP{} -> notSupported "Unboxed sums" (Just (show p))
  ConP _ _ ps -> combine (map boundVars ps)
  InfixP p1 _ p2 -> (<>) <$> boundVars p1 <*> boundVars p2
  p@UInfixP{} -> notSupported "UInfixP" (Just (show p))
  ParensP p -> boundVars p
  TildeP p -> boundVars p
  BangP p -> boundVars p
  AsP n p -> Set.insert n <$> boundVars p
  WildP -> return mempty
  p@RecP{} -> notSupported "Records" (Just (show p))
  ListP ps -> combine (map boundVars ps)
  SigP p _ -> boundVars p
  p@ViewP{} -> notSupported "View patterns" (Just (show p))

combine :: (Monad m, Monoid a) => [m a] -> m a
combine = fmap mconcat . sequence

notSupported :: MonadFail m => String -> Maybe String -> m a
notSupported descr mthing = fail $ descr ++ " not supported in reverseAD" ++ maybe "" (": " ++) mthing

zipWithM3 :: Applicative m => (a -> b -> c -> m d) -> [a] -> [b] -> [c] -> m [d]
zipWithM3 f a b c = traverse (\(x,y,z) -> f x y z) (zip3 a b c)

swap :: (a, b) -> (b, a)
swap (a, b) = (b, a)
