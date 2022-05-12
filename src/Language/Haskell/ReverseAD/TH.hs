{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS -Wno-incomplete-uni-patterns #-}
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
import Control.Monad.State.Strict
import qualified Data.Array.Mutable.Linear as A
import Data.Array.Mutable.Linear (Array)
import Data.Bifunctor (second)
import Data.Foldable (toList)
import Data.Function ((&))
import Data.List (tails, mapAccumL, zip4, unzip5)
import Data.Int
import Data.Proxy
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable
import qualified Data.Vector as V
import Data.Void
import Data.Word
import GHC.Types (Multiplicity(One))
import Language.Haskell.TH
import Language.Haskell.TH.Syntax hiding (lift)
import qualified Prelude.Linear as PL
import Prelude.Linear (Ur(..))

-- import Control.Monad.IO.Class
-- import Debug.Trace

import Language.Haskell.ReverseAD.TH.Orphans ()


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

-- | The structure of a type, as used by the AD transformation. Use
-- 'structureFromTypeable' or 'structureFromType' to construct a 'Structure'.
type Structure = Structure' Void

-- | Analyse the 'Type' and give a 'Structure' that describes the type for use
-- in 'reverseAD''.
structureFromType :: Q Type -> Q Structure
structureFromType ty = ty >>= deriveStructure mempty

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

data SimpleType = VarST Name
                | ConST Name [SimpleType]
  deriving (Show, Eq)

summariseType :: Type -> Either String SimpleType
summariseType = \case
  ConT n -> return $ ConST n []
  VarT n -> return $ VarST n
  ParensT t -> summariseType t
  TupleT k -> return $ ConST (tupleTypeName k) []
  ListT -> return $ ConST ''[] []
  t@AppT{} -> collectApps t []
    where collectApps :: Type -> [SimpleType] -> Either String SimpleType
          collectApps (AppT t1 t2) args =
            summariseType t2 >>= \t2' -> collectApps t1 (t2' : args)
          collectApps t1 args =
            summariseType t1 >>= \t1' -> smartAppsST t1' args
  t -> Left $ "Unsupported type: " ++ pprint t
  where
    smartAppsST :: SimpleType -> [SimpleType] -> Either String SimpleType
    smartAppsST (VarST n) _ = Left $ "Higher-rank type variable not supported in reverse AD: " ++ show n
    smartAppsST (ConST n as) bs = return $ ConST n (as ++ bs)

-- | This does not yet check that scalars do not appear in data types!
--
-- The state maps a type name to all the various instantiations under which it
-- occurs in the type we are analysing. For each instantiation, the 'Map'
-- contains the list of type arguments its type variables are instantiated to,
-- as well as the structure that was computed for this intantiation of that
-- data type.
--
-- The return structure tag is either a tag from the environment map, or an
-- instantiation of a data type (indicated using its type name and its type
-- arguments). If a tag is a data type instantiation, it refers to one of the
-- structures from the state 'Map'.
deriveStructureGroup
  :: Map Name (Structure' (Either (Name, [SimpleType]) tag))
       -- ^ Type /variables/ that are in scope
  -> Map Name [SimpleType]  -- ^ Instantiations of /data types/ in the current stack
                            --     (for polymorphic recursion detection)
  -> SimpleType  -- ^ Type to inspect
  -> StateT (Map Name [([SimpleType], Structure' (Either (Name, [SimpleType]) tag))])
            Q (Structure' (Either (Name, [SimpleType]) tag))
deriveStructureGroup env stack = \case
  VarST n ->
    case Map.lookup n env of
      Just struc -> return struc
      Nothing -> fail $ "Type variable out of scope: " ++ show n

  ConST n []
    | n `elem` [''Int, ''Int8, ''Int16, ''Int32, ''Int64
               ,''Word, ''Word8, ''Word16, ''Word32, ''Word64]
    -> return SDiscrete
    | n == ''Double -> return SScalar
    | n == ''Float -> fail "Only Double is an active type for now (Float isn't)"

  ConST tyname argtys
    | Just prevargtys <- Map.lookup tyname stack ->
        if argtys == prevargtys
          then return (STag (Left (tyname, argtys)))  -- recursion detected!
          else fail $ "Polymorphic recursion (data type that contains itself \
                      \with different type argument instantiations) is not \
                      \supported in reverse AD"

    | otherwise -> do
        -- Compute the structures for the argument types; we do not yet grow
        -- the stack, as these are not data type fields.
        argstrucs <- mapM (deriveStructureGroup env stack) argtys

        -- Get information about the data type
        typedecl <- lift (reify tyname) >>= \case
          TyConI decl -> return decl
          info -> fail $ "Name " ++ show tyname ++ " is not a type name: " ++ show info
        (tyvars, constrs) <- case typedecl of
          NewtypeD [] _ tyvars _ constr  _ -> return (map tvbName tyvars, [constr])
          DataD    [] _ tyvars _ constrs _ -> return (map tvbName tyvars, constrs)
          _ -> fail $ "Type not supported: " ++ show tyname ++ " (not simple newtype or data)"
        when (length tyvars /= length argtys) $
          fail $ "Type not fully applied: " ++ show tyname

        -- Analyse a constructor, and return (constructor name, [field structures])
        let goConstr constr = do
              -- Get constructor name and field types
              (conname, fieldtys) <- case constr of
                NormalC conname fieldtys -> return (conname, map (\(  _,ty) -> ty) fieldtys)
                RecC    conname fieldtys -> return (conname, map (\(_,_,ty) -> ty) fieldtys)
                _ -> fail $ "Unsupported constructor format on data: " ++ show constr
              fieldtys' <- mapM (either fail return . summariseType) fieldtys
              -- - In the field type, the environment contains bindings for the type
              --   variables of the data type the constructor is a member of. In
              --   particular, we forget any other environment bindings we had before.
              -- - We add the current data type to the stack.
              let env' = Map.fromList (zip tyvars argstrucs)
                  stack' = Map.insert tyname argtys stack
              (conname,) <$> mapM (deriveStructureGroup env' stack') fieldtys'

        SData <$> mapM goConstr constrs

deriveStructure :: Map Name (Structure' tag) -> Type -> Q (Structure' tag)
deriveStructure = \env -> go env True
  where
    go :: Map Name (Structure' tag) -> Bool -> Type -> Q (Structure' tag)
    go env scalarsAllowed = \case
      AppT (ConT listty) eltty | listty == ''[] ->
        SList <$> go env scalarsAllowed eltty
      t@AppT{} -> do
        let (headty, argtys) = collectApps t
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
        | n == ''Float
        -> fail "Only Double is an active type for now (Float isn't)"
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
                  constr -> fail $ "Unsupported constructor format on data: " ++ show constr
            SData <$> mapM goConstr constrs
          _ -> fail $ "Type not supported: " ++ show tyname

      _ -> fail $ "Type unsupported in data in reverse AD: " ++ show headty

    collectApps = second reverse . collectAppsRev
    collectAppsRev :: Type -> (Type, [Type])
    collectAppsRev (AppT t1 t2) = second (t2 :) (collectAppsRev t1)
    collectAppsRev (ParensT t) = collectAppsRev t
    collectAppsRev t = (t, [])

-- | Pattern match on the given data constructor and extract the single value.
unNewtype :: Quote m => Name -> Exp -> m Exp
unNewtype conname expr = do
  name <- newName "x"
  return $ CaseE expr [Match (ConP conname [] [VarP name]) (NormalB (VarE name)) []]


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
  argvar <- newName "arg"
  onevar <- newName "one"
  inp <- numberInput inpStruc (VarE argvar) onevar
  rebuildvar <- newName "rebuild"
  idvar <- newName "i0"
  patbound <- boundVars pat
  ddrexpr <- ddr patbound idvar expr
  outname <- newName "out"
  idvar' <- newName "i'"
  deinterexpr <- deinterleave outStruc (VarE outname)
  primalname <- newName "primal"
  dualname <- newName "dual"
  adjname <- newName "adjoint"
  stagedvecname <- newName "stagedvec"
  let composeLinearFuns :: [Exp] -> Exp
      composeLinearFuns [] = VarE 'PL.id
      composeLinearFuns l = foldl1 (\a b -> InfixE (Just a) (VarE '(PL..)) (Just b)) l
  return (LamE [VarP argvar] $
            LetE [ValD (VarP onevar) (NormalB (SigE (LitE (IntegerL 1)) (ConT ''Int))) []
                 ,ValD (TupP [pat, VarP rebuildvar, VarP idvar]) (NormalB inp) []
                 ,ValD (TupP [VarP outname, VarP idvar']) (NormalB ddrexpr) []
                 ,ValD (TupP [VarP primalname, VarP dualname]) (NormalB deinterexpr) []] $
              pair (VarE primalname)
                   (LamE [VarP adjname] $
                      LetE [ValD (ConP 'Ur [] [VarP stagedvecname])
                                 (NormalB
                                    (VarE 'A.alloc
                                       `AppE` VarE idvar'
                                       `AppE` pair (AppE (ConE 'Contrib) (ListE []))
                                                   (LitE (RationalL 0.0))
                                       `AppE` composeLinearFuns
                                                [VarE 'A.freeze
                                                ,AppE (VarE 'resolve) (VarE idvar')
                                                ,AppE (VarE dualname) (VarE adjname)]))
                                 []] $
                        VarE rebuildvar `AppE` (VarE 'V.map `AppE` VarE 'snd `AppE` VarE stagedvecname)))
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
    (exprs, outnames, primnames, bpnames, adjnames) <- fmap unzip5 . forM (zip strucs [1::Int ..]) $ \(struc', index) -> do
      outn <- newName ("out" ++ show index)
      primn <- newName ("prim" ++ show index)
      bpn <- newName ("bp" ++ show index)
      adjn <- newName ("adj" ++ show index)
      expr <- deinterleave struc' (VarE outn)
      return (expr, outn, primn, bpn, adjn)
    case strucs of
      [] -> return (pair (TupE []) (LamE [WildP] (VarE 'PL.id)))
      _ -> return $
        LetE (ValD (TupP (map VarP outnames)) (NormalB outexp) []
             :[ValD (TupP [VarP primn, VarP bpn]) (NormalB expr) []
              | (expr, primn, bpn) <- zip3 exprs primnames bpnames]) $
          pair (TupE (map (Just . VarE) primnames))
               (LamE [TupP (map VarP adjnames)] $
                  foldr1 (\e1 e2 -> VarE '(PL..) `AppE` e1 `AppE` e2)
                         (zipWith AppE (map VarE bpnames) (map VarE adjnames)))

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
    tempvar <- newName "temp"
    unnewtypetemp <- LamE [VarP tempvar] <$> unNewtype conname (VarE tempvar)
    return $ CaseE expr
      [Match (TupP [VarP primalname, VarP dualname])
             (NormalB (pair (ConE conname `AppE` VarE primalname)
                            (InfixE (Just (VarE dualname)) (VarE '(.)) (Just unnewtypetemp))))
             []]

  SData [] ->
    return $ CaseE outexp []

  SData datacons -> do
    let maxlen = maximum [length fieldstrucs | (_, fieldstrucs) <- datacons]
    allvars      <- mapM (\i -> newName ("x"     ++ show i)) [1 .. maxlen]
    allresvars   <- mapM (\i -> newName ("res"   ++ show i)) [1 .. maxlen]
    allbuildvars <- mapM (\i -> newName ("build" ++ show i)) [1 .. maxlen]
    alladjvars   <- mapM (\i -> newName ("adj"   ++ show i)) [1 .. maxlen]
    matches <- sequence
      [do let vars      = take (length fieldstrucs) allvars
              resvars   = take (length fieldstrucs) allresvars
              buildvars = take (length fieldstrucs) allbuildvars
              adjvars   = take (length fieldstrucs) alladjvars
          exprs <- zipWithM deinterleave fieldstrucs (map VarE vars)
          return $ Match
            (ConP conname [] (map VarP vars))
            (NormalB $
               LetE [ValD (TupP [VarP resvar, VarP buildvar]) (NormalB expr) []
                    | (resvar, buildvar, expr) <- zip3 resvars buildvars exprs] $
                 pair (foldl AppE (ConE conname) (map VarE resvars))
                      (LamE [ConP conname [] (map VarP adjvars)] $
                         VarE 'composeL
                           `AppE` ListE [VarE buildvar `AppE` VarE adjvar
                                        | (buildvar, adjvar) <- zip buildvars adjvars]))
            []
      | (conname, fieldstrucs) <- datacons]
    return $ CaseE outexp matches

-- Set of names bound in the program at this point
type Env = Set Name

-- Γ |- i : Int                        -- idName
-- Γ |- t : a                          -- expression
-- ~> Dt[Γ] |- D[i, t] : (Dt[a], Int)  -- result
ddr :: Env -> Name -> Exp -> Q Exp
ddr env idName = \case
  VarE name
    | name `Set.member` env -> return (pair (VarE name) (VarE idName))
    | name == 'fromIntegral -> do  -- TODO: this assumes this produces a Double...
        xname <- newName "x"
        iname <- newName "i"
        -- We add a type signature on the Double in the tuple not because this
        -- is super necessary, but to hopefully make the error message a bit
        -- better if we mis-guessed the result type of fromIntegral.
        return (pair (LamE [VarP xname, VarP iname] $
                        pair (pair (SigE (VarE 'fromIntegral `AppE` VarE xname)
                                         (ConT ''Double))
                                   (pair (VarE iname) (AppE (ConE 'Contrib) (ListE []))))
                             (InfixE (Just (VarE iname))
                                     (VarE '(+))
                                     (Just (LitE (IntegerL 1)))))
                     (VarE idName))
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
        let function = LamE [VarP xname, VarP iname] $
              foldl AppE (VarE 'applyUnaryOp)
                [VarE xname
                ,VarE 'sqrt
                ,LamE [VarP xname] (InfixE (Just (LitE (IntegerL 1))) (VarE '(/)) (Just (InfixE (Just (LitE (IntegerL 2))) (VarE '(*)) (Just (AppE (VarE 'sqrt) (VarE xname))))))
                ,VarE iname]
        return (pair function (VarE idName))
    | name == '($) -> do
        fname <- newName "f"
        xname <- newName "x"
        ddr env idName (LamE [VarP fname, VarP xname] (AppE (VarE fname) (VarE xname)))
    | otherwise -> fail $ "Free variables not supported in reverseAD: " ++ show name ++ " (env = " ++ show env ++ ")"

  ConE name
    | name `elem` ['[]] -> return (pair (ConE name) (VarE idName))
    | otherwise -> do
        fieldtys <- checkDatacon name
        -- let todo = "TODO: kleisli-transform every arrow in the type of the data constructor into the id generation monad"
        conexpr <- liftKleisliN (length fieldtys) (ConE name)
        return (pair conexpr (VarE idName))
        -- fail $ "Data constructor not supported in reverseAD: " ++ show name

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

        handleOther =
          Just $ ddr env idName (AppE (AppE (VarE opname) e1) e2)

    case asum [handleNum, handleOrd, handleOther] of
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

triple :: Exp -> Exp -> Exp -> Exp
triple e1 e2 e3 = TupE [Just e1, Just e2, Just e3]

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
  let appliedType = foldl AppT (ConT tycon) (map VarT tyvars)
  -- The fact that 'deriveStructure' returns successfully implies that the type is fine
  _ <- deriveStructure (Map.fromList (zip tyvars (repeat (STag ())))) appliedType
  return fieldtys

-- | Given the type of a data constructor, return:
-- - the name of the type it is a constructor of;
-- - the instantiations of the type parameters of that type in the types of the constructor's fields;
-- - the types of the fields of the constructor
fromDataconType :: Type -> Maybe (Name, [Type], [Type])
fromDataconType (ForallT _ _ t) = fromDataconType t
fromDataconType (ArrowT `AppT` ty `AppT` t) =
  (\(n, typarams, tys) -> (n, typarams, ty : tys)) <$> fromDataconType t
fromDataconType (MulArrowT `AppT` PromotedT multi `AppT` ty `AppT` t)
  | multi == 'One = (\(n, typarams, tys) -> (n, typarams, ty : tys)) <$> fromDataconType t
  | otherwise = Nothing
fromDataconType t = (\(n, typarams) -> (n, typarams, [])) <$> extractTypeCon t

extractTypeCon :: Type -> Maybe (Name, [Type])
extractTypeCon (AppT t arg) = second (++ [arg]) <$> extractTypeCon t
extractTypeCon (ConT n) = Just (n, [])
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
            case rhs of LamE (_:_) _ -> True
                        _ -> nonRecursive boundAfterThis frees)
         (zip tups (tail (tails (map fst3 tups))))
    then return (Just tups)
    else return Nothing

numberList :: (Int -> a -> (da, V.Vector Double -> a, Int)) -> [a] -> Int -> ([da], V.Vector Double -> [a], Int)
numberList f l i0 =
  let (outi, pairslist) = mapAccumL (\i x -> let (dx, f', i') = f i x in (i', (dx, f'))) i0 l
      (dlist, funs) = unzip pairslist
  in (dlist, \arr -> map ($ arr) funs, outi)

-- input :: a
-- nextid :: Name Int
-- result :: (Dt[a], Vector Double -> a, Int)
numberInput :: Quote m => Structure -> Exp -> Name -> m Exp
numberInput topstruc input nextid = case topstruc of
  SDiscrete -> do
    var <- newName "inpx"
    return $ LetE [ValD (VarP var) (NormalB input) []] $
               triple (VarE var) (LamE [WildP] (VarE var)) (VarE nextid)

  SScalar -> do
    var <- newName "arr"
    return $
      triple (pair input
                   (pair (VarE nextid)
                         (ConE 'Contrib `AppE` ListE [])))
             (LamE [VarP var] (InfixE (Just (VarE var)) (VarE '(V.!)) (Just (VarE nextid))))
             (AppE (VarE 'succ) (VarE nextid))

  STuple strucs -> do
    names <- mapM (const (newName "inp")) strucs
    postnames <- mapM (const (newName "inp'")) strucs
    rebuildnames <- mapM (const (newName "reb")) strucs
    idnames <- zipWithM (\_ i -> newName ("i" ++ show i)) strucs [1::Int ..]
    let outid = case idnames of [] -> nextid ; _ -> last idnames
    exps <- zipWithM3 numberInput strucs (map VarE names) (nextid : idnames)
    arrname <- newName "arr"
    return (LetE (ValD (TupP (map VarP names)) (NormalB input) []
                 : [ValD (TupP [VarP postname, VarP rebuildname, VarP idname]) (NormalB expr) []
                   | (postname, rebuildname, idname, expr) <- zip4 postnames rebuildnames idnames exps])
                 (triple (TupE (map (Just . VarE) postnames))
                         (LamE [VarP arrname] $
                            TupE (map (\f -> Just (VarE f `AppE` VarE arrname)) rebuildnames))
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
    dxvar <- newName "dx"
    fvar <- newName "f"
    i'var <- newName "i'"
    return $ CaseE expr
      [Match (TupP [VarP dxvar, VarP fvar, VarP i'var])
             (NormalB (TupE [Just (ConE conname `AppE` VarE dxvar)
                            ,Just (InfixE (Just (ConE conname)) (VarE '(.)) (Just (VarE fvar)))
                            ,Just (VarE i'var)]))
             []]

  SData datacons -> do
    let maxlen = maximum [length fieldstrucs | (_, fieldstrucs) <- datacons]
    allinnames  <- mapM (\i -> newName ("x"  ++ show i)) [1 .. maxlen]
    alloutnames <- mapM (\i -> newName ("x'" ++ show i)) [1 .. maxlen]
    allfnames   <- mapM (\i -> newName ("f"  ++ show i)) [1 .. maxlen]
    allidnames  <- mapM (\i -> newName ("i"  ++ show i)) [1 .. maxlen]
    arrname <- newName "arr"
    matches <- sequence
      [do let innames  = take (length fieldstrucs) allinnames
              outnames = take (length fieldstrucs) alloutnames
              fnames   = take (length fieldstrucs) allfnames
              idnames  = take (length fieldstrucs) allidnames
              outid = case fieldstrucs of [] -> nextid ; _ -> last idnames
          exprs <- zipWithM3 numberInput fieldstrucs (map VarE innames) (nextid : idnames)
          return $ Match (ConP conname [] (map VarP innames))
                         (NormalB
                            (LetE [ValD (TupP [VarP outname, VarP fname, VarP outidname])
                                        (NormalB expr)
                                        []
                                  | (outname, fname, outidname, expr)
                                      <- zip4 outnames fnames idnames exprs] $
                               triple (foldl AppE (ConE conname) (map VarE outnames))
                                      (LamE [VarP arrname] $
                                         foldl AppE (ConE conname)
                                           (map (\f -> VarE f `AppE` VarE arrname) fnames))
                                      (VarE outid)))
                         []
      | (conname, fieldstrucs) <- datacons]
    return $ CaseE input matches

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

tvbName :: TyVarBndr () -> Name
tvbName (PlainTV n _) = n
tvbName (KindedTV n _ _) = n
