-- TODO:
-- - Polymorphically recursive data types

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
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
  -- * Special methods
  (|*|),
) where

import Control.Applicative (asum)
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Class (lift)
import Control.Parallel (par)
import qualified Data.Array.Mutable.Linear as A
import Data.Array.Mutable.Linear (Array)
import Data.Bifunctor (second)
import Data.Char (isAlphaNum)
import Data.Foldable (toList)
import Data.Function ((&))
import Data.Graph (stronglyConnComp, SCC(..))
import Data.List (zip4)
import Data.Int
import Data.Proxy
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable
import qualified Data.Vector as V
import Data.Word
import GHC.Types (Multiplicity(..))
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
-- Dt[a -> b] = Dt[a] -> FwdM Dt[b]
-- Dt[Int] = Int
-- Dt[T a b c] = T Dt[a] Dt[b] Dt[c]      -- data types, generalises (,)
--
-- Dt[eps] = eps
-- Dt[Γ, x : a] = Dt[Γ], x : Dt[a]
--
-- FwdM is a monad with:
--   gen :: FwdM Int
--
-- Γ |- t : a
-- ~> Dt[Γ] |- D[t] : FwdM Dt[a]
-- D[r] = do i <- gen; pure (r, (i, Contrib []))
-- D[x] = pure x
-- D[()] = ((), i)
-- D[(s, t)] = do x <- D[s]
--                y <- D[t]
--                pure (x, y)
-- D[C s t u] = do x <- D[s]
--                 y <- D[t]
--                 z <- D[u]
--                 pure (C x y z)
-- D[case s of C1 x1 x2 -> t1 ; ... ; Cn x1 x2 -> tn] =
--     do x <- D[s]
--        case x of
--          C1 x1 x2 -> D[t1]
--          ...
--          Cn x1 x2 -> D[tn]
-- D[s t] = do f <- D[s]
--             a <- D[t]
--             f a
-- D[\x -> t] = pure (\x -> D[t])
-- D[let x = s in t] = do x <- D[s]
--                        D[t]
-- D[op t1..tn] =
--   do (x1, (i1, cb1)) = D[t1]
--      (x2, (i2, cb2)) = D[t1]
--      ...
--      (xn, (in, cbn)) = D[tn]
--      i <- gen
--      pure (op x1..xn
--           ,(i, Contrib [(i1, cb1, dop_1 x1..xn), ..., (in, cbn, dop_n x1..xn)]))


-- ----------------------------------------------------------------------
-- Additional API
-- ----------------------------------------------------------------------

-- | Parallel (strict) pair construction.
--
-- The definition of @x |*| y@ is @x \`'par'\` y \`'par'\` (x, y)@: @x@ and @y@
-- are evaluated in parallel. This also means that this pair constructor is
-- strict, in a sense.
--
-- In differentiation using 'reverseAD', this function is specially interpreted
-- so that not only the forward pass, but also the reverse gradient pass runs
-- in parallel. This takes some additional administration, so benchmark whether
-- your parallel work is expensive enough to warrant using this combinator.
(|*|) :: a -> b -> (a, b)
x |*| y = x `par` y `par` (x, y)


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
-- The monad for the target program
-- ------------------------------------------------------------

newtype FwdM a = FwdM (Int -> (Int, a))
  deriving (Functor)

instance Applicative FwdM where
  pure x = FwdM (\i -> (i, x))
  FwdM f <*> FwdM g = FwdM $ \i -> let (j, h) = f i in second h (g j)

instance Monad FwdM where
  FwdM f >>= g = FwdM $ \i -> let (j, x) = f i ; FwdM h = g x in h j

-- Returns highest Id generated plus 1
runFwdM :: FwdM a -> (Int, a)
runFwdM (FwdM f) = f 0

fwdmGenId :: FwdM Int
fwdmGenId = FwdM (\i -> (i + 1, i))


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
  rebuildvar <- newName "rebuild"
  rebuild'var <- newName "rebuild'"
  outvar <- newName "out"
  out'var <- newName "out'"
  ioutvar <- newName "iout"
  primalvar <- newName "primal"
  dualvar <- newName "dual"
  adjvar <- newName "adjoint"
  stagedvecvar <- newName "stagedvec"
  [| \ $(varP argvar) ->
        let ($(varP ioutvar), ($(varP outvar), $(varP rebuildvar))) = runFwdM $ do
              ($(pure pat), $(varP rebuild'var)) <- $(interleave inpStruc (VarE argvar))
              $(varP out'var) <- $(ddr patbound expr)
              pure ($(varE out'var), $(varE rebuild'var))
            ($(varP primalvar), $(varP dualvar)) = $(deinterleave outStruc (VarE outvar))
        in ($(varE primalvar)
           ,\ $(varP adjvar) ->
                let Ur $(varP stagedvecvar) =
                      A.alloc $(varE ioutvar)
                              (Contrib [], 0.0)
                              (A.freeze
                               PL.. resolve $(varE ioutvar)
                               PL.. $(varE dualvar) $(varE adjvar))
                in $(varE rebuildvar) (V.map snd $(varE stagedvecvar))) |]
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

-- Γ |- t : a                        -- expression
-- ~> Dt[Γ] |- D[i, t] : FwdM Dt[a]  -- result
ddr :: Env -> Exp -> Q Exp
ddr env = \case
  VarE name
    | name `Set.member` env -> [| pure $(varE name) |]
    | name == 'fromIntegral -> [| pure fromIntegralOp |]
    | name == 'negate -> do
        xname <- newName "x"
        [| pure (\ $(varP xname) -> applyUnaryOp $(varE xname) negate (\_ -> (-1))) |]
    | name == 'sqrt -> do
        xname <- newName "x"
        pname <- newName "p"
        [| pure (\ $(varP xname) ->
              applyUnaryOp $(varE xname) sqrt (\ $(varP pname) -> 1 / (2 * sqrt $(varE pname)))) |]
    | name == 'exp -> do
        xname <- newName "x"
        primalname <- newName "p"
        [| pure (\ $(varP xname) ->
              applyUnaryOp2 $(varE xname) exp (\_ $(varP primalname) -> $(varE primalname))) |]
    | name == 'log -> do
        xname <- newName "x"
        pname <- newName "p"
        [| pure (\ $(varP xname) ->
              applyUnaryOp $(varE xname) log (\ $(varP pname) -> 1 / $(varE pname))) |]
    | name == 'sin -> do
        xname <- newName "x"
        pname <- newName "p"
        [| pure (\ $(varP xname) ->
              applyUnaryOp $(varE xname) sin (\ $(varP pname) -> cos $(varE pname))) |]
    | name == 'cos -> do
        xname <- newName "x"
        pname <- newName "p"
        [| pure (\ $(varP xname) ->
              applyUnaryOp $(varE xname) cos (\ $(varP pname) -> - sin $(varE pname))) |]
    | name == '($) -> do
        fname <- newName "f"
        xname <- newName "x"
        ddr env (LamE [VarP fname, VarP xname] (AppE (VarE fname) (VarE xname)))
    | name == '(.) -> do
        fname <- newName "f"
        gname <- newName "g"
        xname <- newName "x"
        ddr env (LamE [VarP fname, VarP gname, VarP xname] (AppE (VarE fname) (AppE (VarE gname) (VarE xname))))
    | name `elem` ['(+), '(-), '(*), '(/)] -> do
        xname <- newName "x"
        yname <- newName "y"
        ddr env (LamE [VarP xname, VarP yname] (InfixE (Just (VarE xname)) (VarE name) (Just (VarE yname))))
    | name == 'error -> [| pure error |]
    | name == 'fst -> [| pure (pure . fst) |]
    | name == 'snd -> [| pure (pure . snd) |]
    | otherwise -> fail $ "Free variables not supported in reverseAD: " ++ show name ++ " (env = " ++ show env ++ ")"

  ConE name
    | otherwise -> do
        fieldtys <- checkDatacon name
        (VarE 'pure `AppE`) <$> liftKleisliN (length fieldtys) (ConE name)

  LitE lit -> case lit of
    RationalL _ -> do
      iname <- newName "i"
      [| do $(varP iname) <- fwdmGenId
            pure ($(litE lit), ($(varE iname), Contrib [])) |]
    FloatPrimL _ -> fail "float prim?"
    DoublePrimL _ -> fail "double prim?"
    IntegerL _ -> [| pure $(litE lit) |]
    StringL _ -> [| pure $(litE lit) |]
    _ -> fail $ "literal? " ++ show lit

  AppE e1 e2 -> do
    (wrap, [funname, argname]) <- ddrList env [e1, e2]
    return (wrap (VarE funname `AppE` VarE argname))

  -- Handle ($) specially in case the program needs the special type inference (let's hope it does not)
  InfixE (Just e1) (VarE opname) (Just e2) | opname == '($) ->
    ddr env (AppE e1 e2)

  InfixE (Just e1) (VarE opname) (Just e2) | opname == '(|*|) ->
    ddr env (TupE [Just e1, Just e2])

  InfixE (Just e1) (VarE opname) (Just e2) -> do
    let handleNum =
          if | opname == '(+) -> Just ((False, False), \_ _ -> [| (1, 1) |])
             | opname == '(-) -> Just ((False, False), \_ _ -> [| (1, (-1)) |])
             | opname == '(*) -> Just ((True, True), \x y -> [| ($y, $x) |])
             | opname == '(/) -> Just ((True, True), \x y -> [| (recip $y, (- $x) / ($y * $y)) |])
             | otherwise -> Nothing
            & \case
              Nothing -> Nothing
              Just ((gxused, gyused), gradientfun) -> Just $ do
                (wrap, [x1name, x2name]) <- ddrList env [e1, e2]
                t1name <- newName "arg1"
                t2name <- newName "arg2"
                wrap <$>
                  [| applyBinaryOp
                       $(varE x1name) $(varE x2name) $(varE opname)
                       (\ $(if gxused then varP t1name else wildP)
                          $(if gyused then varP t2name else wildP) ->
                            $(gradientfun (varE t1name) (varE t2name))) |]

        handleOrd =
          if opname `elem` ['(==), '(/=), '(<), '(>), '(<=), '(>=)]
            then Just $ do
              (wrap, [x1name, x2name]) <- ddrList env [e1, e2]
              t1name <- newName "arg1"
              t2name <- newName "arg2"
              return $ wrap $ VarE 'pure `AppE`
                foldl AppE (VarE 'applyCmpOp)
                  [VarE x1name, VarE x2name
                  ,LamE [VarP t1name, VarP t2name] $
                     InfixE (Just (VarE t1name)) (VarE opname) (Just (VarE t2name))]
            else Nothing

        handleOther =  -- TODO: can we just put an infix operator in a VarE?
          ddr env (VarE opname `AppE` e1 `AppE` e2)

    fromMaybe handleOther (asum [handleNum, handleOrd])

  InfixE (Just e1) (ConE constr) (Just e2) ->
    ddr env (ConE constr `AppE` e1 `AppE` e2)

  e@InfixE{} -> fail $ "Unsupported operator section: " ++ show e

  ParensE e -> ParensE <$> ddr env e

  LamE [pat] e -> do
    patbound <- boundVars pat
    e' <- ddr (env <> patbound) e
    [| pure (\ $(pure pat) -> $(pure e')) |]

  TupE mes | Just es <- sequence mes -> do
    (wrap, vars) <- ddrList env es
    return (wrap $ VarE 'pure `AppE` TupE (map (Just . VarE) vars))

  CondE e1 e2 e3 -> do
    e1' <- ddr env e1
    boolName <- newName "bool"
    e2' <- ddr env e2
    e3' <- ddr env e3
    return (DoE Nothing
              [BindS (VarP boolName) e1'
              ,NoBindS (CondE (VarE boolName) e2' e3')])

  LetE decs body -> do
    decs' <- mapM desugarDec decs
    ddrDecs env decs' >>= \case
      Just (wrap, vars, _) -> do
        body' <- ddr (env <> Set.fromList vars) body
        return $ wrap body'
      Nothing ->
        notSupported "Recursive non-function declarations in let" (Just (show (LetE decs body)))

  CaseE expr matches -> do
    (wrap, [evar]) <- ddrList env [expr]
    matches' <- sequence
      [case mat of
         Match pat (NormalB rhs) [] -> do
           patbound <- boundVars pat
           pat' <- ddrPat pat
           rhs' <- ddr (env <> patbound) rhs
           return (pat', rhs')
         _ -> fail "Where blocks or guards not supported in case expressions"
      | mat <- matches]
    return $ wrap $
      CaseE (VarE evar)
        [Match pat (NormalB rhs) [] | (pat, rhs) <- matches']

  ListE es -> do
    (wrap, vars) <- ddrList env es
    return (wrap (VarE 'pure `AppE` ListE (map VarE vars)))

  SigE e ty ->
    SigE <$> ddr env e <*> ((ConT ''FwdM `AppT`) <$> ddrType ty)

  UnboundVarE n -> fail $ "Free variable in reverseAD: " ++ show n

  -- Constructs that we can express in terms of other, simpler constructs handled above
  LamE [] e -> ddr env e  -- is this even a valid AST?
  LamE (pat : pats@(_:_)) e -> ddr env (LamE [pat] (LamE pats e))
  LamCaseE mats -> do
    name <- newName "lcarg"
    ddr env (LamE [VarP name] (CaseE (VarE name) mats))

  -- tuple sections (these were excluded by the TupE case above)
  TupE mes -> do
    let trav _ [] argsf esf = return (argsf [], esf [])
        trav i (Nothing : mes') argsf esf = do
          name <- newName ("x" ++ show (i :: Int))
          trav (i+1) mes' (argsf . (name :)) (esf . (VarE name :))
        trav i (Just e : mes') argsf esf =
          trav i mes' argsf (esf . (e :))

    (args, es) <- trav 1 mes id id
    ddr env (LamE (map VarP args) (TupE (map Just es)))

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
  e@RecConE{} -> notSupported "Records" (Just (show e))
  e@RecUpdE{} -> notSupported "Records" (Just (show e))
  e@StaticE{} -> notSupported "Cloud Haskell" (Just (show e))
  e@LabelE{} -> notSupported "Overloaded labels" (Just (show e))
  e@ImplicitParamVarE{} -> notSupported "Implicit parameters" (Just (show e))
  e@GetFieldE{} -> notSupported "Records" (Just (show e))
  e@ProjectionE{} -> notSupported "Records" (Just (show e))
  e -> notSupported (takeWhile (/= ' ') (show e)) (Just (show e))

-- | Given list of expressions, returns a wrapper that defines a variable for
-- each item in the list (differentiated), together with a list of the names of
-- those variables.
-- The expressions must all have the same, given, environment.
ddrList :: Env -> [Exp] -> Q (Exp -> Exp, [Name])
ddrList env es = do
  names <- mapM (\idx -> newName ("x" ++ show idx)) [1 .. length es]
  rhss <- mapM (ddr env) es
  return (\rest ->
            DoE Nothing $ [BindS (VarP nx) e | (nx, e) <- zip names rhss] ++ [NoBindS rest]
         ,names)

-- | Assumes the declarations occur in a let block. If non-recursive (apart
-- from function bindings), returns a wrapper that defines all of the names,
-- the list of defined names, and the set of all free variables of the
-- collective let-block.
ddrDecs :: Env -> [Dec] -> Q (Maybe (Exp -> Exp, [Name], Set Name))
ddrDecs env decs = do
  bindings <- flip traverse decs $ \case
    ValD (VarP name) (NormalB e) [] -> return (name, e)
    dec -> notSupported "Declaration in let" (Just (show dec))

  let extendedEnv = env <> Set.fromList (map fst bindings)

  let processDec :: Dec -> Q (Name, Set Name, Exp)
      processDec = \case
        ValD (VarP name) (NormalB e) [] -> do
          frees <- freeVars extendedEnv e
          return (name, frees, e)
        dec -> fail $ "Unsupported declaration in let: " ++ show dec

      fromLam :: Exp -> Maybe (Pat, Exp)
      fromLam (LamE (p : vs) e) = Just (p, LamE vs e)
      fromLam (LamE [] e) = fromLam e
      fromLam (ParensE e) = fromLam e
      fromLam _ = Nothing

      handleComp :: Env -> SCC (Name, Exp) -> MaybeT Q Stmt
      handleComp env' (AcyclicSCC (name, e)) = BindS (VarP name) <$> lift (ddr env' e)
      handleComp env' (CyclicSCC (unzip -> (names, es)))
        | Just (unzip -> (pats, bodies)) <- traverse fromLam es = lift $ do
            bounds <- traverse boundVars pats
            bodies' <- traverse
                         (\(bound, body) -> ddr (env' <> Set.fromList names <> bound) body)
                         (zip bounds bodies)
            pure $ LetS [ValD (VarP name) (NormalB (LamE [pat] body)) []
                        | (name, pat, body) <- zip3 names pats bodies']
        | otherwise =
            MaybeT (return Nothing)

      handleComps :: Env -> [SCC (Name, Exp)] -> MaybeT Q [Stmt]
      handleComps _ [] = return []
      handleComps env' (comp : comps) = do
        let bound = case comp of
                      AcyclicSCC (name, _) -> [name]
                      CyclicSCC ps -> map fst ps
        stmt <- handleComp env' comp
        stmts <- handleComps (env' <> Set.fromList bound) comps
        return (stmt : stmts)

  tups <- mapM processDec decs
  let sccs = stronglyConnComp (map (\(name, frees, e) -> ((name, e), name, toList frees)) tups)
  mstmts <- runMaybeT $ handleComps env sccs
  let declared = map fst3 tups

  case mstmts of
    Nothing -> return Nothing
    Just stmts -> return $ Just
                    (\rest -> DoE Nothing $ stmts ++ [NoBindS rest]
                    ,declared
                    ,Set.unions [frees | (_, frees, _) <- tups] Set.\\ Set.fromList declared)

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

ddrType :: Type -> Q Type
ddrType = \ty ->
  case go ty of
    Left bad -> fail $ "Don't know how to differentiate (" ++ show bad ++ "), which is a \
                       \part of the type: " ++ show ty
    Right res -> return res
  where
    go :: Type -> Either Type Type
    go (ConT name)
      | name == ''Double = Right (pairt (ConT ''Double) (pairt (ConT ''Int) (ConT ''Contrib)))
      | name == ''Int = Right (ConT ''Int)
    go (ArrowT `AppT` t1 `AppT` t) = do
      t1' <- go t1
      t' <- go t
      return $ ArrowT `AppT` t1' `AppT` (ConT ''FwdM `AppT` t')
    go (MulArrowT `AppT` PromotedT multi `AppT` t1 `AppT` t)
      | multi == 'Many = go (ArrowT `AppT` t1 `AppT` t)
    go ty =
      case second ($ []) (collectApps ty) of
        (TupleT n, args) | length args == n ->
          foldl AppT (TupleT n) <$> traverse go args
        (ConT name, args) ->  -- I hope this one is correct
          foldl AppT (ConT name) <$> traverse go args
        _ -> Left ty  -- don't know how to handle this type

    collectApps :: Type -> (Type, [Type] -> [Type])
    collectApps (t1 `AppT` t2) = second (. (t2:)) (collectApps t1)
    collectApps t = (t, id)

    pairt :: Type -> Type -> Type
    pairt t1 t2 = TupleT 2 `AppT` t1 `AppT` t2


-- ----------------------------------------------------------------------
-- The wrapper: interleave and deinterleave
-- ----------------------------------------------------------------------

-- input :: a
-- result :: FwdM (Dt[a], Vector Double -> a)
interleave :: Quote m => Structure -> Exp -> m Exp
interleave (Structure monotype dtypemap) input = do
  helpernames <- Map.fromAscList <$>
                   sequence [((n, ts),) <$> newName (genDataNameTag "inter" n ts)
                            | (n, ts) <- Map.keys dtypemap]
  helperfuns <- sequence [(helpernames Map.! (n, ts),) <$> interleaveData helpernames constrs
                         | ((n, ts), constrs) <- Map.assocs dtypemap]
  mainfun <- interleaveType helpernames monotype
  return $ LetE [ValD (VarP name) (NormalB fun) []
                | (name, fun) <- helperfuns] $
             mainfun `AppE` input

-- Given constructors of type T, returns expression of type
-- 'T -> (Dt[T], Vector Double -> T)'. The Map contains for each
-- (type name T', type arguments As') combination that occurs (transitively) in
-- T, the name of a function with type
-- 'T' As' -> (Dt[T' As'], Vector Double -> T' As')'.
interleaveData :: Quote m => Map (Name, [MonoType]) Name -> [(Name, [MonoType])] -> m Exp
interleaveData helpernames constrs = do
  inputvar <- newName "input"
  let maxn = maximum (map (length . snd) constrs)
  allinpvars     <- mapM (\i -> newName ("inp"  ++ show i)) [1..maxn]
  allpostvars    <- mapM (\i -> newName ("inp'" ++ show i)) [1..maxn]
  allrebuildvars <- mapM (\i -> newName ("reb"  ++ show i)) [1..maxn]
  -- These have the inpvars in scope.
  bodies <- sequence
    [do -- For constructor C f₁…f₃:
        --   do (post₁, rebuild₁) <- $(interleaveType helpernames f₁) inp₁
        --      (post₂, rebuild₂) <- $(interleaveType helpernames f₂) inp₂
        --      (post₃, rebuild₃) <- $(interleaveType helpernames f₃) inp₃
        --      pure (C post₁ post₂ post₃
        --           ,\arr -> C (rebuild₁ arr) (rebuild₂ arr) (rebuild₃ arr))
        --
        -- interleaveType helpernames (Monotype for T) :: Exp (T -> FwdM (Dt[T], Vector Double -> T))
        let inpvars = take (length fieldtys) allinpvars
            postvars = take (length fieldtys) allpostvars
            rebuildvars = take (length fieldtys) allrebuildvars
        exps <- mapM (interleaveType helpernames) fieldtys
        arrname <- newName "arr"
        return $ DoE Nothing $
          [BindS (TupP [VarP postvar, VarP rebuildvar])
                 (expr `AppE` VarE inpvar)
          | (inpvar, postvar, rebuildvar, expr)
               <- zip4 inpvars postvars rebuildvars exps]
          ++
          [NoBindS $ VarE 'pure `AppE`
              pair (foldl AppE (ConE conname) (map VarE postvars))
                   (LamE [if null rebuildvars then WildP else VarP arrname] $
                      foldl AppE (ConE conname)
                            [VarE f `AppE` VarE arrname | f <- rebuildvars])]
    | (conname, fieldtys) <- constrs]

  -- \input -> case input of
  --   C₁ inp₁ inp₂ inp₃ -> $(bodies !! 0)
  --   C₂ inp₁ inp₂      -> $(bodies !! 1)
  --   C₃ inp₁ inp₂ inp₃ -> $(bodies !! 2)
  return $ LamE [VarP inputvar] $ CaseE (VarE inputvar)
    [Match (ConP conname [] (map VarP inpvars))
           (NormalB body)
           []
    | ((conname, fieldtys), body) <- zip constrs bodies
    , let inpvars = take (length fieldtys) allinpvars]

-- Given a type T, returns expression of type
-- 'T -> FwdM (Dt[T], Vector Double -> T)'. The Map contains for each
-- (type name T', type arguments As') combination that occurs in the type, the
-- name of a function with type
-- 'T' As' -> FwdM (Dt[T' As'], Vector Double -> T' As')'.
interleaveType :: Quote m => Map (Name, [MonoType]) Name -> MonoType -> m Exp
interleaveType helpernames = \case
  DiscreteST -> do
    inpxvar <- newName "inpx"
    [| \ $(varP inpxvar) -> pure ($(varE inpxvar), \_ -> $(varE inpxvar)) |]

  ScalarST -> do
    inpxvar <- newName "inpx"
    ivar <- newName "i"
    arrvar <- newName "arr"
    [| \ $(varP inpxvar) -> do
           $(varP ivar) <- fwdmGenId
           pure (($(varE inpxvar), ($(varE ivar), Contrib []))
                ,\ $(varP arrvar) -> $(varE arrvar) V.! $(varE ivar)) |]

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
    -> FwdM (DualNum a)        -- output
  applyUnaryOp
    :: DualNum a               -- argument
    -> (a -> a)                -- primal
    -> (a -> a)                -- derivative given input (assuming adjoint 1)
    -> FwdM (DualNum a)        -- output
  applyUnaryOp2
    :: DualNum a               -- argument
    -> (a -> a)                -- primal
    -> (a -> a -> a)           -- derivative given input and primal result (assuming adjoint 1)
    -> FwdM (DualNum a)        -- output
  applyCmpOp
    :: DualNum a -> DualNum a  -- arguments
    -> (a -> a -> Bool)        -- primal
    -> Bool                    -- output
  fromIntegralOp
    :: Integral b
    => b                       -- argument
    -> FwdM (DualNum a)        -- output

instance NumOperation Double where
  type DualNum Double = (Double, (Int, Contrib))
  applyBinaryOp (x, (xi, xcb)) (y, (yi, ycb)) primal grad = do
    let (dx, dy) = grad x y
    i <- fwdmGenId
    pure (primal x y, (i, Contrib [(xi, xcb, dx), (yi, ycb, dy)]))
  applyUnaryOp (x, (xi, xcb)) primal grad = do
    i <- fwdmGenId
    pure (primal x, (i, Contrib [(xi, xcb, grad x)]))
  applyUnaryOp2 (x, (xi, xcb)) primal grad = do
    i <- fwdmGenId
    let pr = primal x
    pure (pr, (i, Contrib [(xi, xcb, grad x pr)]))
  applyCmpOp (x, _) (y, _) f = f x y
  fromIntegralOp x = do
    i <- fwdmGenId
    pure (fromIntegral x, (i, Contrib []))

instance NumOperation Int where
  type DualNum Int = Int
  applyBinaryOp x y primal _ = pure (primal x y)
  applyUnaryOp x primal _ = pure (primal x)
  applyUnaryOp2 x primal _ = pure (primal x)
  applyCmpOp x y f = f x y
  fromIntegralOp x = pure (fromIntegral x)


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
-- > \x1 -> pure (\x2 -> pure (... \xn -> pure (e x1 ... xn)))
liftKleisliN :: Int -> Exp -> Q Exp
liftKleisliN 0 e = return e
liftKleisliN n e = do
  name <- newName "x"
  [| \ $(varP name) -> pure $(liftKleisliN (n - 1) (e `AppE` VarE name)) |]

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

freeVars :: Env -> Exp -> Q (Set Name)
freeVars env = \case
  VarE n -> return (Set.singleton n)
  ConE{} -> return mempty
  LitE{} -> return mempty
  AppE e1 e2 -> (<>) <$> freeVars env e1 <*> freeVars env e2
  AppTypeE e1 _ -> freeVars env e1
  InfixE me1 e2 me3 -> combine [maybe (return mempty) (freeVars env) me1
                               ,freeVars env e2
                               ,maybe (return mempty) (freeVars env) me3]
  e@UInfixE{} -> notSupported "UInfixE" (Just (show e))
  ParensE e -> freeVars env e
  LamE pats e -> do
    bound <- combine (map boundVars pats)
    frees <- freeVars (env <> bound) e
    return (frees Set.\\ bound)
  LamCaseE mats ->
    combine [case mat of
               Match pat (NormalB e) [] -> do
                 bound <- boundVars pat
                 frees <- freeVars (env <> bound) e
                 return (frees Set.\\ bound)
               _ -> notSupported "Pattern in LambdaCase (neither guards nor where-blocks supported)" (Just (show mat))
            | mat <- mats]
  TupE es -> combine (map (maybe (return mempty) (freeVars env)) es)
  UnboxedTupE es -> combine (map (maybe (return mempty) (freeVars env)) es)
  e@UnboxedSumE{} -> notSupported "Unboxed sums" (Just (show e))
  CondE e1 e2 e3 -> combine (map (freeVars env) [e1, e2, e3])
  e@MultiIfE{} -> notSupported "Multi-way ifs" (Just (show e))
  LetE decs body -> do
    ddrDecs env decs >>= \case
      Just (_, bound, frees) -> (frees <>) <$> freeVars (env <> Set.fromList bound) body
      Nothing -> notSupported "Recursive declarations in let" (Just (show (LetE decs body)))
  CaseE e ms -> (<>) <$> freeVars env e <*> combine (map go ms)
    where go :: Match -> Q (Set Name)
          go (Match pat (NormalB rhs) []) = do
            bound <- boundVars pat
            frees <- freeVars (env <> bound) rhs
            return (frees Set.\\ bound)
          go mat = fail $ "Unsupported match in case: " ++ show mat
  e@DoE{} -> notSupported "Do blocks" (Just (show e))
  e@MDoE{} -> notSupported "MDo blocks" (Just (show e))
  e@CompE{} -> notSupported "List comprehensions" (Just (show e))
  e@ArithSeqE{} -> notSupported "Arithmetic sequences" (Just (show e))
  ListE es -> combine (map (freeVars env) es)
  SigE e _ -> freeVars env e
  e@RecConE{} -> notSupported "Records" (Just (show e))
  e@RecUpdE{} -> notSupported "Records" (Just (show e))
  e@StaticE{} -> notSupported "Cloud Haskell" (Just (show e))
  UnboundVarE n -> return (Set.singleton n)
  e@LabelE{} -> notSupported "Overloaded labels" (Just (show e))
  e@ImplicitParamVarE{} -> notSupported "Implicit parameters" (Just (show e))
  e@GetFieldE{} -> notSupported "Records" (Just (show e))
  e@ProjectionE{} -> notSupported "Records" (Just (show e))
  e -> notSupported (takeWhile (/= ' ') (show e)) (Just (show e))

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

notSupported :: MonadFail m => String -> Maybe String -> m a
notSupported descr mthing = fail $ descr ++ " not supported in reverseAD" ++ maybe "" (": " ++) mthing

tvbName :: TyVarBndr () -> Name
tvbName (PlainTV n _) = n
tvbName (KindedTV n _ _) = n

mapUnionsWithKey :: (Foldable f, Ord k) => (k -> a -> a -> a) -> f (Map k a) -> Map k a
mapUnionsWithKey f = foldr (Map.unionWithKey f) mempty

fst3 :: (a, b, c) -> a
fst3 (a, _, _) = a
