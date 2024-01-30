-- TODO:
-- - Polymorphically recursive data types

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS -Wno-incomplete-uni-patterns #-}

-- This warning is over-eager in TH quotes when the variables that the pattern
-- binds are spliced instead of mentioned directly. See
-- https://gitlab.haskell.org/ghc/ghc/-/issues/22057 .
{-# OPTIONS -Wno-unused-pattern-binds #-}

module Language.Haskell.ReverseAD.TH (
  -- * Reverse AD
  reverseAD,
  reverseAD',
  -- * Structure descriptions
  Structure,
  structureFromTypeable,
  structureFromType,
) where

import Control.Applicative (asum)
import qualified Data.Array.Mutable.Linear as A
import Data.Array.Mutable.Linear (Array)
import Data.Bifunctor (second)
import Data.Char (isAlphaNum)
import Data.Foldable (toList)
import Data.Function ((&))
import Data.List (tails, zip6, zip4)
import Data.Int
import Data.Proxy
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable
import qualified Data.Vector as V
import Data.Word
import GHC.Types (Multiplicity(One))
import Language.Haskell.TH
import Language.Haskell.TH.Syntax hiding (lift)
import qualified Prelude.Linear as PL
import Prelude.Linear (Ur(..))

-- import Control.Monad.IO.Class
-- import Debug.Trace

import Language.Haskell.ReverseAD.TH.Orphans ()


-- === The program transformation ===
--
-- Dt[Double] = (Double, (Int, Contrib))
-- Dt[()] = ()
-- Dt[(a, b)] = (Dt[a], Dt[b])
-- Dt[a -> b] = Dt[a] -> Int -> (Dt[b], Int)
-- Dt[Int] = Int
-- Dt[T a b c] = T Dt[a] Dt[b] Dt[c]      -- data types, generalises (,)
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
-- D[i, C x y z] = let (x', i1) = D[i, x]
--                     (y', i2) = D[i1, y]
--                     (z', i3) = D[i2, z]
--                 in (C x' y' z', i3)
-- D[i, case s of C1 x1 x2 -> t1 ; ... ; Cn x1 x2 -> tn] =
--        let (x, i1) = D[i, s]
--        in case x of
--          C1 x1 x2 -> D[i1, t1]
--          ...
--          Cn x1 x2 -> D[i1, tn]
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


-- ----------------------------------------------------------------------
-- The State type
-- ----------------------------------------------------------------------

type BuildState = Array (Contrib, Double)
newtype Contrib = Contrib [(Int, Contrib, Double)]

resolve :: Int -> BuildState %1-> BuildState
resolve iout = \arr -> loop (iout - 1) arr
  where
    loop :: Int -> BuildState %1-> BuildState
    loop 0 arr = arr
    loop i arr =
      A.get i arr PL.& \(Ur (cb, adj), arr1) ->
        loop (i - 1) (apply cb adj arr1)

    apply :: Contrib -> Double -> BuildState %1-> BuildState
    apply (Contrib []) _ arr = arr
    apply (Contrib ((i, cb, d) : cbs)) a arr =
      A.get i arr PL.& \(Ur (_, acc), arr1) ->  -- acc = backpropagator argument (i.e. adjoint) accumulator
      A.set i (cb, acc + a * d) arr1 PL.& \arr2 ->
        apply (Contrib cbs) a arr2

addContrib :: Int -> Contrib -> Double -> BuildState %1-> BuildState
addContrib i cb adj arr =
  A.get i arr PL.& \(Ur (_, acc), arr1) ->
    A.set i (cb, acc + adj) arr1


-- ------------------------------------------------------------
-- Structure descriptions of types
-- ------------------------------------------------------------

-- | The structure of a type, as used by the AD transformation. Use
-- 'structureFromTypeable' or 'structureFromType' to construct a 'Structure'.
data Structure = Structure MonoType DataTypes
  deriving (Show)

-- | Analyse the 'Type' and give a 'Structure' that describes the type for use
-- in 'reverseAD''.
structureFromType :: Q Type -> Q Structure
structureFromType ty = ty >>= fmap (uncurry Structure) . exploreRecursiveType

-- | A 'TypeRep' (which we can obtain from the 'Typeable' constraint) can be
-- used to construct a 'Type' for the type @a@, on which we can then call
-- 'structureFromType'.
structureFromTypeable :: Typeable a => Proxy a -> Q Structure
structureFromTypeable = structureFromType . typeRepToType . typeRep
  where
    -- Taken from th-utilities-0.2.4.3 by Michael Sloan
    typeRepToType :: TypeRep -> Q Type
    typeRepToType tr = do
      let (con, args) = splitTyConApp tr
          name = Name (OccName (tyConName con)) (NameG TcClsName (PkgName (tyConPackage con)) (ModName (tyConModule con)))
      resultArgs <- mapM typeRepToType args
      return (foldl AppT (ConT name) resultArgs)

data Morphic = Poly | Mono
  deriving (Show)

data SimpleType morphic where
  DiscreteST :: SimpleType mf
  ScalarST :: SimpleType mf
  VarST :: Name -> SimpleType 'Poly
  ConST :: Name -> [SimpleType mf] -> SimpleType mf
deriving instance Show (SimpleType mf)
deriving instance Eq (SimpleType mf)
deriving instance Ord (SimpleType mf)
deriving instance Lift (SimpleType mf)

type PolyType = SimpleType 'Poly
type MonoType = SimpleType 'Mono

summariseType :: MonadFail m => Type -> m PolyType
summariseType = \case
  ConT n
    | n `elem` [''Int, ''Int8, ''Int16, ''Int32, ''Int64
               ,''Word, ''Word8, ''Word16, ''Word32, ''Word64
               ,''Char]
    -> return DiscreteST
    | n == ''Double -> return ScalarST
    | n == ''Float -> fail "Only Double is an active type for now (Float isn't)"
    | otherwise -> return $ ConST n []
  VarT n -> return $ VarST n
  ParensT t -> summariseType t
  TupleT k -> return $ ConST (tupleTypeName k) []
  ListT -> return $ ConST ''[] []
  t@AppT{} -> collectApps t []
  t -> fail $ "Unsupported type: " ++ pprint t
  where
    collectApps :: MonadFail m => Type -> [PolyType] -> m PolyType
    collectApps (AppT t1 t2) args = do
      t2' <- summariseType t2
      collectApps t1 (t2' : args)
    collectApps t1 args = summariseType t1 >>= \t1' -> smartAppsST t1' args

    smartAppsST :: MonadFail m => PolyType -> [PolyType] -> m PolyType
    smartAppsST DiscreteST _ = fail $ "Discrete type does not take type parameters"
    smartAppsST ScalarST _ = fail $ "'Double' does not take type parameters"
    smartAppsST (VarST n) _ = fail $ "Higher-rank type variable not supported in reverse AD: " ++ show n
    smartAppsST (ConST n as) bs = return $ ConST n (as ++ bs)

-- | Given an inlining function that returns the value of a type /variable/,
-- monomorphise the type.
toMonoType :: Applicative f => (Name -> f MonoType) -> PolyType -> f MonoType
toMonoType _ DiscreteST = pure DiscreteST
toMonoType _ ScalarST = pure ScalarST
toMonoType f (VarST n) = f n
toMonoType f (ConST n ts) = ConST n <$> traverse (toMonoType f) ts

-- Map from (type name, type arguments) to [(constructor name, fields)]
type DataTypes = Map (Name, [MonoType]) [(Name, [MonoType])]

-- | Given:
-- - The stack of types in the current exploration branch (initialise with
--   'mempty'), giving for each type name its argument instantiation
-- - The current type synonym expansion stack
-- - The monotype to explore
-- returns the transitive closure of datatypes included in the input monotype.
exploreType :: Map Name [MonoType] -> Set Name -> MonoType -> Q DataTypes
exploreType stack tysynstack
  | Map.size stack >= 20 = \_ -> fail "Very deep data type hierarchy (depth 20); polymorphic recursion?"
  | Set.size tysynstack >= 20 = \_ -> fail "Very deep type synonym hierarchy (depth 20); self-recursive type synonym?"
exploreType stack tysynstack = \case
  DiscreteST -> return mempty
  ScalarST -> return mempty
  ConST tyname argtys
    | Just prevargtys <- Map.lookup tyname stack
    , argtys == prevargtys -> return mempty
        -- if argtys == prevargtys
        --   then return mempty  -- regular recursion, don't need to expand again
        --   else fail $ "Polymorphic recursion (data type that contains itself \
        --               \with different type argument instantiations) is not \
        --               \supported in reverse AD.\n\
        --               \Type constructor: " ++ show tyname ++ "\n\
        --               \Previously seen: " ++ show prevargtys ++ "\n\
        --               \Current:         " ++ show argtys
    | otherwise -> do
        typedecl <- reify tyname >>= \case
          TyConI decl -> return decl
          info -> fail $ "Name " ++ show tyname ++ " is not a lifted type name: "
                         ++ show info
        let analyseConstructor tyvars constr
              | length tyvars == length argtys = do
                  (conname, fieldtys) <- case constr of
                    NormalC conname fieldtys -> return (conname, map (\(  _,ty) -> ty) fieldtys)
                    RecC    conname fieldtys -> return (conname, map (\(_,_,ty) -> ty) fieldtys)
                    InfixC (_, ty1) conname (_, ty2) -> return (conname, [ty1, ty2])
                    _ -> fail $ "Unsupported constructor format on data: " ++ show constr
                  fieldtys' <- mapM summariseType fieldtys
                  fieldtys'' <- mapM (monomorphiseField tyname tyvars argtys) fieldtys'
                  let stack' = Map.insert tyname argtys stack
                  typesets <- mapM (exploreType stack' mempty) fieldtys''
                  return ((conname, fieldtys''), mapUnionsWithKey mergeIfEqual typesets)
              | otherwise = fail $ "Type not fully applied: " ++ show tyname
        case typedecl of
          NewtypeD [] _ tyvars _ constr  _ -> do
            (condescr, typeset) <- analyseConstructor (map tvbName tyvars) constr
            return (Map.insertWithKey mergeIfEqual (tyname, argtys) [condescr] typeset)
          DataD    [] _ tyvars _ constrs _ -> do
            (condescrs, typesets) <- unzip <$> mapM (analyseConstructor (map tvbName tyvars)) constrs
            let typeset = mapUnionsWithKey mergeIfEqual typesets
            return (Map.insertWithKey mergeIfEqual (tyname, argtys) condescrs typeset)
          TySynD _ tyvars rhs -> do
            -- when (tyname `Set.member` tysynstack) $
            --   fail $ "Infinite type synonym recursion in " ++ show tyname
            srhs <- summariseType rhs
            mrhs <- monomorphiseField tyname (map tvbName tyvars) argtys srhs
            exploreType stack (Set.insert tyname tysynstack) mrhs
          _ -> fail $ "Type not supported: " ++ show tyname ++ " (not simple \
                      \newtype or data)"
  where
    monomorphiseField :: Name -> [Name] -> [MonoType] -> PolyType -> Q MonoType
    monomorphiseField tyname typarams argtys =
      toMonoType $ \n -> case lookup n (zip typarams argtys) of
        Just mt -> return mt
        Nothing -> fail $ "Type variable out of scope in definition of \
                          \data type " ++ show tyname ++ ": " ++ show n

    mergeIfEqual key v1 v2
      | v1 == v2 = v1
      | otherwise = error $ "Conflicting explorations of the same data type!\n\
                            \Key: " ++ show key ++ "\n\
                            \Val 1: " ++ show v1 ++ "\n\
                            \Val 2: " ++ show v2

exploreRecursiveType :: Type -> Q (MonoType, DataTypes)
exploreRecursiveType tau = do
  sty <- summariseType tau
  mty <- toMonoType (\n -> fail $ "Reverse AD input or output type is polymorphic \
                                  \(contains type variable " ++ show n ++ ")")
                    sty
  dtypes <- exploreType mempty mempty mty
  return (mty, dtypes)


-- ----------------------------------------------------------------------
-- Top-level interface to reverse AD
-- ----------------------------------------------------------------------

-- | Use as follows:
--
-- > > :t $$(reverseAD @_ @Double [|| \(x, y) -> x * y ||])
-- > (Double, Double) -> (Double, Double -> (Double, Double))
--
-- The active scalar type is 'Double'. 'Double' values are differentiated; 'Float' is currently unsupported.
--
-- Note that due to the GHC stage restriction, any data types used in @a@ and
-- @b@ must be defined in a separate module that is then imported into the
-- module where you use 'reverseAD'. If you get a GHC panic about @$tcFoo@ not
-- being in scope (where @Foo@ is your data type), this means that you violated
-- this stage restriction. See
-- [GHC #21547](https://gitlab.haskell.org/ghc/ghc/-/issues/21547).
reverseAD :: forall a b. (Typeable a, Typeable b)
          => Code Q (a -> b)
          -> Code Q (a -> (b, b -> a))
reverseAD = reverseAD' (structureFromTypeable (Proxy @a)) (structureFromTypeable (Proxy @b))

-- | Same as 'reverseAD', but with user-supplied 'Structure's.
reverseAD' :: forall a b.
              Q Structure  -- ^ Structure of @a@
           -> Q Structure  -- ^ Structure of @b@
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
  patbound <- boundVars pat
  argvar <- newName "arg"
  onevar <- newName "one"
  rebuildvar <- newName "rebuild"
  idvar <- newName "i0"
  outname <- newName "out"
  idvar' <- newName "i'"
  primalname <- newName "primal"
  dualname <- newName "dual"
  adjname <- newName "adjoint"
  stagedvecname <- newName "stagedvec"
  [| \ $(varP argvar) ->
        let $(varP onevar) = 1 :: Int
            ($(pure pat), $(varP rebuildvar), $(varP idvar)) = $(interleave inpStruc (VarE argvar) onevar)
            ($(varP outname), $(varP idvar')) = $(ddr patbound idvar expr)
            ($(varP primalname), $(varP dualname)) = $(deinterleave outStruc (VarE outname))
        in ($(varE primalname)
           ,\ $(varP adjname) ->
                let Ur $(varP stagedvecname) =
                      A.alloc $(varE idvar')
                              (Contrib [], 0.0)
                              (A.freeze
                               PL.. resolve $(varE idvar')
                               PL.. $(varE dualname) $(varE adjname))
                in $(varE rebuildvar) (V.map snd $(varE stagedvecname))) |]
transform inpStruc outStruc (LamE [] body) =
  transform inpStruc outStruc body
transform inpStruc outStruc (LamE (pat : pats) body) =
  transform inpStruc outStruc (LamE [pat] (LamE pats body))
transform _ _ expr =
  fail $ "Top-level expression in reverseAD must be lambda, but is: " ++ show expr


-- ----------------------------------------------------------------------
-- The compositional code transformation
-- ----------------------------------------------------------------------

-- Set of names bound in the program at this point
type Env = Set Name

-- Γ |- i : Int                        -- idName
-- Γ |- t : a                          -- expression
-- ~> Dt[Γ] |- D[i, t] : (Dt[a], Int)  -- result
ddr :: Env -> Name -> Exp -> Q Exp
ddr env idName = \case
  VarE name
    | name `Set.member` env -> return (pair (VarE name) (VarE idName))
    | name == 'fromIntegral -> return (pair (VarE 'fromIntegralOp) (VarE idName))
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
    | name == 'sqrt -> do
        xname <- newName "x"
        iname <- newName "i"
        let bin a op b = InfixE (Just a) (VarE op) (Just b)
            lit = LitE . IntegerL
        let function = LamE [VarP xname, VarP iname] $
              foldl AppE (VarE 'applyUnaryOp)
                [VarE xname
                ,VarE 'sqrt
                ,LamE [VarP xname] (bin (lit 1) '(/) (bin (lit 2) '(*) (AppE (VarE 'sqrt) (VarE xname))))
                ,VarE iname]
        return (pair function (VarE idName))
    | name == '($) -> do
        fname <- newName "f"
        xname <- newName "x"
        ddr env idName (LamE [VarP fname, VarP xname] (AppE (VarE fname) (VarE xname)))
    | otherwise -> fail $ "Free variables not supported in reverseAD: " ++ show name ++ " (env = " ++ show env ++ ")"

  ConE name
    | otherwise -> do
        fieldtys <- checkDatacon name
        conexpr <- liftKleisliN (length fieldtys) (ConE name)
        return (pair conexpr (VarE idName))

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

        handleOther =  -- TODO: can we just put an infix operator in a VarE?
          Just $ ddr env idName (VarE opname `AppE` e1 `AppE` e2)

    case asum [handleNum, handleOrd, handleOther] of
      Nothing -> fail ("Unsupported infix operator " ++ show opname)
      Just act -> act

  InfixE (Just e1) (ConE constr) (Just e2) ->
    ddr env idName (ConE constr `AppE` e1 `AppE` e2)

  e@InfixE{} -> fail $ "Unsupported operator section: " ++ show e

  ParensE e -> ParensE <$> ddr env idName e

  LamE [pat] e -> do
    idName1 <- newName "i"
    patbound <- boundVars pat
    e' <- ddr (env <> patbound) idName1 e
    return (pair (LamE [pat, VarP idName1] e') (VarE idName))

  TupE mes | Just es <- sequence mes -> do
    (letwrap, vars, outid) <- ddrList env es idName
    return (letwrap (pair (TupE (map (Just . VarE) vars))
                          (VarE outid)))

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

  TupE mes -> do
    let trav _ [] argsf esf = return (argsf [], esf [])
        trav i (Nothing : mes') argsf esf = do
          name <- newName ("x" ++ show (i :: Int))
          trav (i+1) mes' (argsf . (name :)) (esf . (VarE name :))
        trav i (Just e : mes') argsf esf =
          trav i mes' argsf (esf . (e :))

    (args, es) <- trav 1 mes id id
    ddr env idName (LamE (map VarP args) (TupE (map Just es)))

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

-- | Given list of expressions and the input ID, returns a let-wrapper that
-- defines a variable for each item in the list (differentiated), the names of
-- those variables, and the output ID name (in scope in the let-wrapper).
-- The expressions must all have the same, given, environment.
ddrList :: Env -> [Exp] -> Name -> Q (Exp -> Exp, [Name], Name)
ddrList env es idName = do
  -- output varnames of the expressions
  names <- mapM (\idx -> (,) <$> newName ("x" ++ show idx) <*> newName ("i" ++ show idx))
                [1 .. length es]
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
        -- ignore the field types; just validity is good enough, assuming that the user's code was okay
        _ <- checkDatacon name
        ConP name [] <$> traverse ddrPat args
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


-- ----------------------------------------------------------------------
-- The wrapper: interleave and deinterleave
-- ----------------------------------------------------------------------

-- input :: a
-- nextid :: Name Int
-- result :: (Dt[a], Vector Double -> a, Int)
interleave :: Quote m => Structure -> Exp -> Name -> m Exp
interleave (Structure monotype dtypemap) input nextid = do
  let dtypes = Map.keys dtypemap
  helpernames <- Map.fromAscList <$>
                   sequence [((n, ts),) <$> newName (genDataNameTag "inter" n ts)
                            | (n, ts) <- dtypes]
  helperfuns <- sequence [(helpernames Map.! (n, ts),) <$> interleaveData helpernames constrs
                         | ((n, ts), constrs) <- Map.assocs dtypemap]
  mainfun <- interleaveType helpernames monotype
  return $ LetE [ValD (VarP name) (NormalB fun) []
                | (name, fun) <- helperfuns] $
             mainfun `AppE` input `AppE` VarE nextid

-- Given constructors of type T, returns expression of type
-- 'T -> Int -> (Dt[T], Vector Double -> T, Int)'. The Map contains for each
-- (type name T', type arguments As') combination that occurs (transitively) in
-- T, the name of a function with type
-- 'T' As' -> Int -> (Dt[T' As'], Vector Double -> T' As', Int)'.
interleaveData :: Quote m => Map (Name, [MonoType]) Name -> [(Name, [MonoType])] -> m Exp
interleaveData helpernames constrs = do
  inputvar <- newName "input"
  idvar0 <- newName "i0"
  let maxn = maximum (map (length . snd) constrs)
  allinpvars     <- mapM (\i -> newName ("inp"  ++ show i)) [1..maxn]
  allpostvars    <- mapM (\i -> newName ("inp'" ++ show i)) [1..maxn]
  allrebuildvars <- mapM (\i -> newName ("reb"  ++ show i)) [1..maxn]
  allidvars      <- mapM (\i -> newName ("i"    ++ show i)) [1..maxn]
  -- These have the inpvars and idvar0 in scope.
  bodies <- sequence
    [do let inpvars = take (length fieldtys) allinpvars
            postvars = take (length fieldtys) allpostvars
            rebuildvars = take (length fieldtys) allrebuildvars
            idvars = take (length fieldtys) allidvars
        let finalidvar = case idvars of [] -> idvar0 ; _ -> last idvars
        -- interleaveType helpernames (MonoType T) :: Exp (T -> Int -> (Dt[T], Vector Double -> T, Int))
        exps <- mapM (interleaveType helpernames) fieldtys
        arrname <- newName "arr"
        return $ LetE [ValD (TupP [VarP postvar, VarP rebuildvar, VarP outidvar])
                            (NormalB (expr `AppE` VarE inpvar `AppE` VarE inidvar))
                            []
                      | (inpvar, postvar, rebuildvar, inidvar, outidvar, expr)
                           <- zip6 inpvars postvars rebuildvars (idvar0 : idvars) idvars exps] $
                   triple (foldl AppE (ConE conname) (map VarE postvars))
                          (LamE [if null rebuildvars then WildP else VarP arrname] $
                             foldl AppE (ConE conname)
                                   [VarE f `AppE` VarE arrname | f <- rebuildvars])
                          (VarE finalidvar)
    | (conname, fieldtys) <- constrs]

  return $ LamE [VarP inputvar, VarP idvar0] $ CaseE (VarE inputvar)
    [Match (ConP conname [] (map VarP inpvars))
           (NormalB body)
           []
    | ((conname, fieldtys), body) <- zip constrs bodies
    , let inpvars = take (length fieldtys) allinpvars]

-- Given a type T, returns expression of type
-- 'T -> Int -> (Dt[T], Vector Double -> T, Int)'. The Map contains for each
-- (type name T', type arguments As') combination that occurs in the type, the
-- name of a function with type
-- 'T' As' -> Int -> (Dt[T' As'], Vector Double -> T' As', Int)'.
interleaveType :: Quote m => Map (Name, [MonoType]) Name -> MonoType -> m Exp
interleaveType helpernames = \case
  DiscreteST -> do
    inpxvar <- newName "inpx"
    ivar <- newName "i"
    return $ LamE [VarP inpxvar, VarP ivar] $
      triple (VarE inpxvar) (LamE [WildP] (VarE inpxvar)) (VarE ivar)

  ScalarST -> do
    inpxvar <- newName "inpx"
    ivar <- newName "i"
    arrvar <- newName "arr"
    return $ LamE [VarP inpxvar, VarP ivar] $
      triple (pair (VarE inpxvar)
                   (pair (VarE ivar)
                         (ConE 'Contrib `AppE` ListE [])))
             (LamE [VarP arrvar] (InfixE (Just (VarE arrvar)) (VarE '(V.!)) (Just (VarE ivar))))
             (InfixE (Just (VarE ivar)) (VarE '(+)) (Just (LitE (IntegerL 1))))

  ConST tyname argtys ->
    return $ VarE $ case Map.lookup (tyname, argtys) helpernames of
                      Just name -> name
                      Nothing -> error $ "Helper name not defined? " ++ show (tyname, argtys)

-- outexp :: Dt[T]                            -- interleaved program output
-- result :: (T                               -- primal result
--           ,T -> BuildState -o BuildState)  -- given adjoint, add initial contributions
deinterleave :: Quote m => Structure -> Exp -> m Exp
deinterleave (Structure monotype dtypemap) outexp = do
  let dtypes = Map.keys dtypemap
  helpernames <- Map.fromAscList <$>
                   sequence [((n, ts),) <$> newName (genDataNameTag "deinter" n ts)
                            | (n, ts) <- dtypes]
  helperfuns <- sequence [(helpernames Map.! (n, ts),) <$> deinterleaveData helpernames constrs
                         | ((n, ts), constrs) <- Map.assocs dtypemap]
  mainfun <- deinterleaveType helpernames monotype
  return $ LetE [ValD (VarP name) (NormalB fun) []
                | (name, fun) <- helperfuns] $
             mainfun `AppE` outexp

-- Dt[T]                                 -- interleaved program output
--   -> (T                               -- primal result
--      ,T -> BuildState -o BuildState)  -- given adjoint, add initial contributions
-- The Map contains for each (type name T', type arguments As') combination
-- that occurs (transitively) in T, the name of a function with type
-- 'Dt[T' As'] -> (T' As', T' As' -> BuildState -o BuildState)'.
deinterleaveData :: Quote m => Map (Name, [MonoType]) Name -> [(Name, [MonoType])] -> m Exp
deinterleaveData helpernames constrs = do
  dualvar <- newName "out"
  let maxn = maximum (map (length . snd) constrs)
  alldvars <- mapM (\i -> newName ("d" ++ show i)) [1..maxn]
  allpvars <- mapM (\i -> newName ("p" ++ show i)) [1..maxn]
  allfvars <- mapM (\i -> newName ("f" ++ show i)) [1..maxn]
  allavars <- mapM (\i -> newName ("a" ++ show i)) [1..maxn]

  let composeLfuns [] = VarE 'PL.id
      composeLfuns l = foldr1 (\a b -> InfixE (Just a) (VarE '(PL..)) (Just b)) l

  bodies <- sequence
    [do let dvars = take (length fieldtys) alldvars
            pvars = take (length fieldtys) allpvars
            fvars = take (length fieldtys) allfvars
            avars = take (length fieldtys) allavars
        exps <- mapM (deinterleaveType helpernames) fieldtys
        return $ LetE [ValD (TupP [VarP pvar, VarP fvar]) (NormalB (expr `AppE` VarE dvar)) []
                      | (dvar, pvar, fvar, expr) <- zip4 dvars pvars fvars exps] $
                   pair (foldl AppE (ConE conname) (map VarE pvars))
                        -- irrefutable (partial) pattern: that's what you get with sum types in
                        -- a non-dependent context.
                        (LamE [ConP conname [] (map VarP avars)] $
                           SigE (composeLfuns [VarE fvar `AppE` VarE avar
                                              | (fvar, avar) <- zip fvars avars])
                                (MulArrowT `AppT` ConT 'One `AppT` ConT ''BuildState `AppT` ConT ''BuildState))
    | (conname, fieldtys) <- constrs]

  return $ LamE [VarP dualvar] $ CaseE (VarE dualvar)
    [Match (ConP conname [] (map VarP dvars))
           (NormalB body)
           []
    | ((conname, fieldtys), body) <- zip constrs bodies
    , let dvars = take (length fieldtys) alldvars]

-- Dt[T]                                 -- interleaved program output
--   -> (T                               -- primal result
--      ,T -> BuildState -o BuildState)  -- given adjoint, add initial contributions
-- The Map contains for each (type name T', type arguments As') combination
-- that occurs (transitively) in T, the name of a function with type
-- 'Dt[T' As'] -> (T' As', T' As' -> BuildState -o BuildState)'.
deinterleaveType :: Quote m => Map (Name, [MonoType]) Name -> MonoType -> m Exp
deinterleaveType helpernames = \case
  DiscreteST -> do
    dname <- newName "d"
    return $ LamE [VarP dname] $ pair (VarE dname) (LamE [WildP] (VarE 'PL.id))

  ScalarST -> do
    primalname <- newName "prim"
    idname <- newName "id"
    cbname <- newName "cb"
    return $ LamE [TupP [VarP primalname, TupP [VarP idname, VarP cbname]]] $
      pair (VarE primalname)
           (VarE 'addContrib `AppE` VarE idname `AppE` VarE cbname)  -- partially-applied

  ConST tyname argtys ->
    return $ VarE $ case Map.lookup (tyname, argtys) helpernames of
                      Just name -> name
                      Nothing -> error $ "Helper name not defined? " ++ show (tyname, argtys)

-- | Not necessarily unique.
genDataNameTag :: String -> Name -> [MonoType] -> String
genDataNameTag prefix tyname argtys = prefix ++ goN tyname ++ concatMap (('_':) . goT) argtys
  where
    goN :: Name -> String
    goN n = case filter isAlphaNum (show n) of [] -> "xx" ; s -> s

    goT :: MonoType -> String
    goT DiscreteST = "i"
    goT ScalarST = "s"
    goT (ConST n ts) = goN n ++ concatMap goT ts


-- ----------------------------------------------------------------------
-- Polymorphic numeric operations
-- ----------------------------------------------------------------------
--
-- This is to get around the limitation of TH that we do not know the inferred
-- types of subexpressions in the AD transformation. Hence, for polymorphic
-- primitive operations, we defer the choice of implementation to the Haskell
-- typechecker using a type class.

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
  fromIntegralOp
    :: Integral b
    => b                       -- argument
    -> Int                     -- nextid
    -> (DualNum a, Int)        -- output and nextid

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
  fromIntegralOp x nextid = ((fromIntegral x, (nextid, Contrib [])), nextid + 1)

instance NumOperation Int where
  type DualNum Int = Int
  applyBinaryOp x y primal _ nextid = (primal x y, nextid)
  applyUnaryOp x primal _ nextid = (primal x, nextid)
  applyCmpOp x y f = f x y
  fromIntegralOp x nextid = (fromIntegral x, nextid)


-- ----------------------------------------------------------------------
-- Further utility functions
-- ----------------------------------------------------------------------

-- | Returns the types of the fields of the data constructor if valid
checkDatacon :: Name -> Q [Type]
checkDatacon name = do
  conty <- reifyType name
  (tycon, tyargs, fieldtys) <- case fromDataconType conty of
    Just ty -> return ty
    Nothing -> fail $ "Could not deduce root type from type of data constructor " ++ pprint name
  tyvars <- case traverse (\case VarT n -> Just n
                                 _ -> Nothing)
                          tyargs of
              Just vars -> return vars
              Nothing -> fail "Normal constructor has GADT properties?"
  -- Check that we can successfully derive the structure of the type applied to
  -- all-() type arguments. This _should_ be equivalent to a more general
  -- analysis that considers the type variables actual abstract entities.
  let appliedType = foldl AppT tycon (map (\_ -> ConT ''()) tyvars)
  _ <- exploreRecursiveType appliedType
  return fieldtys

-- | Given the type of a data constructor, return:
-- - the name of the type it is a constructor of (usually 'ConT name', but also 'TupleT n');
-- - the instantiations of the type parameters of that type in the types of the constructor's fields;
-- - the types of the fields of the constructor
fromDataconType :: Type -> Maybe (Type, [Type], [Type])
fromDataconType (ForallT _ _ t) = fromDataconType t
fromDataconType (ArrowT `AppT` ty `AppT` t) =
  (\(n, typarams, tys) -> (n, typarams, ty : tys)) <$> fromDataconType t
fromDataconType (MulArrowT `AppT` PromotedT multi `AppT` ty `AppT` t)
  | multi == 'One = (\(n, typarams, tys) -> (n, typarams, ty : tys)) <$> fromDataconType t
  | otherwise = Nothing
fromDataconType t = (\(n, typarams) -> (n, typarams, [])) <$> extractTypeCon t

extractTypeCon :: Type -> Maybe (Type, [Type])
extractTypeCon (AppT t arg) = second (++ [arg]) <$> extractTypeCon t
extractTypeCon (ConT n) = Just (ConT n, [])
extractTypeCon ListT = Just (ConT ''[], [])
extractTypeCon (TupleT n) = Just (TupleT n, [])
extractTypeCon _ = Nothing

-- | Given an expression `e`, wraps it in `n` kleisli-lifted lambdas like
--
-- > \x1 i1 -> (\x2 i2 -> (... \xn in -> (e x1 ... xn, in), i2), i1)
liftKleisliN :: Int -> Exp -> Q Exp
liftKleisliN 0 e = return e
liftKleisliN n e = do
  name <- newName "x"
  e' <- liftKleisliN (n - 1) (AppE e (VarE name))
  iname <- newName "i"
  return (LamE [VarP name, VarP iname] $ pair e' (VarE iname))

-- Convert function declarations to simple variable declarations:
--   f a b c = E
--   f d e f = F
-- becomes
--   f = \arg1 arg2 arg3 -> case (arg1, arg2, arg3) of
--                            (a, b, c) -> E
--                            (d, e, f) -> F
desugarDec :: (Quote m, MonadFail m) => Dec -> m Dec
desugarDec = \case
  dec@(ValD (VarP _) (NormalB _) []) -> return $ dec

  FunD _ [] -> fail "Function declaration with empty list of clauses?"

  FunD name clauses@(_:_)
    | not (allEqual [length pats | Clause pats _ _ <- clauses])
    -> fail "Clauses of a function declaration do not all have the same number of arguments"
    | length [() | Clause _ _ [] <- clauses] /= length clauses
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
            case rhs of LamE (_:_) _ -> True  -- mutually recursive _functions_ are fine
                        _ -> nonRecursive boundAfterThis frees)
         (zip tups (tail (tails (map fst3 tups))))
    then return (Just tups)
    else return Nothing

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

pair :: Exp -> Exp -> Exp
pair e1 e2 = TupE [Just e1, Just e2]

triple :: Exp -> Exp -> Exp -> Exp
triple e1 e2 e3 = TupE [Just e1, Just e2, Just e3]

notSupported :: MonadFail m => String -> Maybe String -> m a
notSupported descr mthing = fail $ descr ++ " not supported in reverseAD" ++ maybe "" (": " ++) mthing

zipWithM3 :: Applicative m => (a -> b -> c -> m d) -> [a] -> [b] -> [c] -> m [d]
zipWithM3 f a b c = traverse (\(x,y,z) -> f x y z) (zip3 a b c)

tvbName :: TyVarBndr () -> Name
tvbName (PlainTV n _) = n
tvbName (KindedTV n _ _) = n

mapUnionsWithKey :: (Foldable f, Ord k) => (k -> a -> a -> a) -> f (Map k a) -> Map k a
mapUnionsWithKey f = foldr (Map.unionWithKey f) mempty

fst3 :: (a, b, c) -> a
fst3 (a, _, _) = a
