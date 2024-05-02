-- TODO:
-- - Polymorphically recursive data types

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS -fno-cse -fno-full-laziness #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE Strict, StrictData #-}
{-# LANGUAGE RankNTypes #-}

-- This warning is over-eager in TH quotes when the variables that the pattern
-- binds are spliced instead of mentioned directly. See
-- https://gitlab.haskell.org/ghc/ghc/-/issues/22057 . Fixed in GHC 9.6.1.
-- {-# OPTIONS -Wno-unused-pattern-binds #-}

module Language.Haskell.ReverseAD.TH (
  -- * Reverse AD
  reverseAD,
  reverseAD_tm,
  reverseAD',
  -- * Structure descriptions
  Structure,
  structureFromTypeable,
  structureFromType,
  -- * Special methods
  (|*|),

  evlog,
) where

import Control.Concurrent
import Control.Monad (when, forM_)
import Control.Parallel (par)
import Data.Bifunctor (first, second)
import Data.Char (isAlphaNum)
import Data.List (zip4, intercalate)
import Data.Int (Int8, Int16, Int32, Int64)
import Data.IORef
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector.Storable.Mutable as MVS
import Data.Word (Word8, Word16, Word32, Word64)
import GHC.Exts (Multiplicity(..))
import Language.Haskell.TH
import Language.Haskell.TH.Syntax as TH hiding (lift)
import System.Clock
import System.IO.Unsafe

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8
import Control.DeepSeq
import Control.Exception (evaluate)

import Control.Monad.IO.Class
-- import Debug.Trace
import System.IO

import Control.Concurrent.ThreadPool
import Data.Vector.Storable.Mutable.CAS
import Language.Haskell.ReverseAD.TH.Orphans ()
import Language.Haskell.ReverseAD.TH.Source as Source
import Language.Haskell.ReverseAD.TH.Translate


-- | Whether to enable debug prints in the differentiation code. This is quite
-- spammy and should be turned off when not actually debugging.
kDEBUG :: Bool
kDEBUG = False


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
-- are evaluated in parallel. This also means that this pair constructor is, in
-- a certain sense, strict.
--
-- In differentiation using 'reverseAD', this function is specially interpreted
-- so that not only the forward pass, but also the reverse gradient pass runs
-- in parallel.
(|*|) :: a -> b -> (a, b)
x |*| y = x `par` y `par` (x, y)


-- ------------------------------------------------------------
-- The monad for the target program
-- ------------------------------------------------------------

-- | The ID of a parallel job, >=0. The implicit main job has ID 0, parallel
-- jobs start from 1.
newtype JobID = JobID Int
  deriving (Show)

data BeforeJob
  = Start  -- ^ Source of (this part of the) graph
  | Fork !JobDescr !JobDescr !JobDescr
      -- ^ a b c: a forked into b and c, which joined into the current job
  deriving (Show)

data JobDescr = JobDescr
    !BeforeJob
    {-# UNPACK #-} !JobID   -- ^ The ID of this job
    {-# UNPACK #-} !Int     -- ^ Number of IDs generated in this thread (i.e. last ID + 1)
  deriving (Show)

newtype FwdM a = FwdM
    (IORef JobID  -- the next job ID to generate
  -> JobDescr  -- job so far
  -> (JobDescr -> a -> IO ()) -> IO ())  -- the terminal job of this computation

instance Functor FwdM where
  fmap f (FwdM g) = FwdM $ \jr !jd k ->
    g jr jd $ \ !jd1 !x ->
      k jd1 (f x)

instance Applicative FwdM where
  pure !x = FwdM (\_ !jd k -> k jd x)
  FwdM f <*> FwdM g = FwdM $ \jr !jd k ->
    f jr jd $ \ !jd1 !fun ->
      g jr jd1 $ \ !jd2 !x ->
        k jd2 (fun x)

instance Monad FwdM where
  FwdM f >>= g = FwdM $ \jr !jd k ->
    f jr jd $ \ !jd1 !x ->
      let FwdM h = g x
      in h jr jd1 k

instance MonadIO FwdM where
  liftIO m = FwdM $ \_ !jd k -> m >>= k jd

-- | 'pure' with a restricted type.
mpure :: a -> FwdM a
mpure = pure

-- runFwdM :: FwdM a -> (JobDescr, JobID, a)
-- runFwdM = runFwdM' Nothing

-- Returns:
-- - the terminal job, i.e. the job with which the computation ended
-- - the maximal job ID generated plus 1
{-# NOINLINE runFwdM' #-}
runFwdM' :: Maybe (IORef Double) -> FwdM a -> (JobDescr, JobID, a)
runFwdM' mfwdtmref (FwdM f) = unsafePerformIO $ do
  evlog "fwdm start"
  tstart <- getTime Monotonic
  jiref <- newIORef (JobID 1)
  resvar <- newEmptyMVar
  _ <- submitJob globalThreadPool (f jiref (JobDescr Start (JobID 0) 0) (curry (putMVar resvar))) return
  -- f jiref (JobDescr Start (JobID 0) 0) (curry (putMVar resvar))
  (jd, y) <- takeMVar resvar
  nextji <- readIORef jiref
  evlog "fwdm end"
  tend <- getTime Monotonic
  forM_ mfwdtmref $ \ref -> writeIORef ref (fromIntegral (toNanoSecs (diffTimeSpec tstart tend)) / 1e9)
  -- hPutStrLn stderr $ "fwdm: " ++ show (fromIntegral (toNanoSecs (diffTimeSpec tstart tend)) / 1e6 :: Double) ++ "ms"
  return (jd, nextji, y)

-- 'a' and 'b' are computed in new, separate jobs.
fwdmPar :: FwdM a -> FwdM b -> FwdM (a, b)
fwdmPar (FwdM f1) (FwdM f2) = FwdM $ \jr !jd0 k -> do
  (ji1, ji2, ji3) <-
    atomicModifyIORef' jr (\(JobID j) -> (JobID (j + 3), (JobID j, JobID (j+1), JobID (j+2))))
  debug "! Starting fork"
  cell1 <- newEmptyMVar
  cell2 <- newEmptyMVar
  forkJoin globalThreadPool
    (f1 jr (JobDescr Start ji1 0) (\jd1 x -> debug "! join left" >> putMVar cell1 (jd1, x)))
    (f2 jr (JobDescr Start ji2 0) (\jd2 y -> debug "! join right" >> putMVar cell2 (jd2, y)))
    (\() () -> do
      (jd1, x) <- takeMVar cell1
      (jd2, y) <- takeMVar cell2
      debug "! Joined"
      _ <- submitJob globalThreadPool (k (JobDescr (Fork jd0 jd1 jd2) ji3 0) (x, y)) return
      return ())

-- | The tag on a node in the Contrib graph. Consists of a job ID and the ID of
-- the node within this thread.
data NID = NID {-# UNPACK #-} !JobID
               {-# UNPACK #-} !Int
  deriving (Show)

fwdmGenId :: FwdM NID
fwdmGenId = FwdM $ \_ (JobDescr prev ji i) k -> k (JobDescr prev ji (i + 1)) (NID ji i)

fwdmGenIdInterleave :: FwdM Int
fwdmGenIdInterleave = FwdM $ \_ (JobDescr prev ji@(JobID jiInt) i) k ->
  if jiInt == 0
    then k (JobDescr prev ji (i + 1)) i
    else error "fwdmGenIdInterleave: not on main thread"


-- ----------------------------------------------------------------------
-- The State type
-- ----------------------------------------------------------------------

-- | For each thread, the unzipped vector of (Contrib, adjoint) pairs. The
-- inner "vector" is Nothing while the items are still being allocated in
-- 'allocBS'.
type MaybeBuildState = MV.IOVector (Maybe (MV.IOVector Contrib, MVS.IOVector Double))
type BuildState = MV.IOVector (MV.IOVector Contrib, MVS.IOVector Double)

-- contrib edge: edge in the contribution graph
data CEdge = CEdge {-# UNPACK #-} !NID
                   !Contrib
                   {-# UNPACK #-} !Double

data Contrib
  = C0
  | C1 {-# UNPACK #-} !CEdge
  | C2 {-# UNPACK #-} !CEdge {-# UNPACK #-} !CEdge
  | C3 ![CEdge]

debugContrib :: Contrib -> String
debugContrib C0 = "Contrib []"
debugContrib (C1 e) = "Contrib [" ++ debugCEdge e ++ "]"
debugContrib (C2 e1 e2) = "Contrib [" ++ debugCEdge e1 ++ "," ++ debugCEdge e2 ++ "]"
debugContrib (C3 l) = "Contrib [" ++ intercalate "," (map debugCEdge l) ++ "]"

debugCEdge :: CEdge -> String
debugCEdge (CEdge nid _ d) = "(" ++ show nid ++ ", <>, " ++ show d ++ ")"

-- TODO: This function is sequential in the total number of jobs started in the
-- forward pass, which is technically not good: they were started in parallel,
-- so we are technically sequentialising a bit in the worst case here. It's not
-- _so_ bad, though.
allocBS :: JobDescr -> MaybeBuildState -> IO ()
allocBS topjobdescr threads = go topjobdescr
  where
    go :: JobDescr -> IO ()
    go (JobDescr prev (JobID ji) n) = do
      -- hPutStrLn stderr $ "allocBS: ji=" ++ show ji
      MV.read threads ji >>= \case
        Just _ -> error $ "allocBS: already allocated? (" ++ show ji ++ ")"
        Nothing -> do
          cbarr <- MV.replicate n C0
          adjarr <- MVS.replicate n 0.0
          MV.write threads ji (Just (cbarr, adjarr))
      case prev of
        Start -> return ()
        Fork parent jd1 jd2 -> do
          go jd1
          go jd2
          go parent

resolve :: JobDescr -> BuildState -> IO ()
resolve terminalJob threads = do
  cell <- newEmptyMVar
  _ <- submitJob globalThreadPool (resolveTask terminalJob (putMVar cell ())) return
  takeMVar cell
  -- resolveTask terminalJob (return ())
  where
    resolveTask :: JobDescr -> IO () -> IO ()
    resolveTask (JobDescr prev ji i) k = do
      when kDEBUG $ hPutStrLn stderr $ "Enter job " ++ show ji ++ " from i=" ++ show (i - 1)
      (cbarr, adjarr) <- MV.read threads (let JobID j = ji in j)
      resolveJob ji (i - 1) cbarr adjarr
      case prev of
        Start -> k
        Fork jd0 jd1 jd2 -> do
          let jidOf (JobDescr _ n _) = n
          when kDEBUG $ hPutStrLn stderr $ "Forking jobs (" ++ show (jidOf jd1) ++ ") and (" ++ show (jidOf jd2) ++ "); parent (" ++ show (jidOf jd0) ++ ")"
          cell1 <- newEmptyMVar
          cell2 <- newEmptyMVar
          forkJoin globalThreadPool
            (resolveTask jd1 (putMVar cell1 ()))
            (resolveTask jd2 (putMVar cell2 ()))
            (\_ _ -> do takeMVar cell1 >> takeMVar cell2
                        _ <- submitJob globalThreadPool (resolveTask jd0 k) return
                        return ())

    resolveJob :: JobID -> Int -> MV.IOVector Contrib -> MVS.IOVector Double -> IO ()
    resolveJob _ (-1) _ _ = return ()
    resolveJob jid i cbarr adjarr = do
      cb <- MV.read cbarr i
      adj <- MVS.read adjarr i
      when kDEBUG $
        liftIO $ hPutStrLn stderr $ "Apply (" ++ show (NID jid i) ++ ") [adj=" ++ show adj ++ "]: " ++ debugContrib cb
      apply cb adj
      resolveJob jid (i - 1) cbarr adjarr

    apply :: Contrib -> Double -> IO ()
    apply C0 _ = return ()
    apply (C1 e) a = applyEdge a e
    apply (C2 e1 e2) a = applyEdge a e1 >> applyEdge a e2
    apply (C3 l) a = mapM_ (applyEdge a) l

    applyEdge a (CEdge nid cb d) = addContrib nid cb (a * d) threads

-- This is the function called from the backpropagator built by deinterleave,
-- as well as from 'resolve'.
addContrib :: NID -> Contrib -> Double -> BuildState -> IO ()
addContrib (NID (JobID ji) i) cb adj threads = do
  (cbarr, adjarr) <- MV.read threads ji
  MV.write cbarr i cb
  let loop acc = do
        (success, old) <- casIOVectorDouble adjarr i acc (acc + adj)
        if success then return () else loop old
  orig <- MVS.read adjarr i
  loop orig
  -- hPutStrLn stderr $ "aC: [" ++ show ji ++ "] " ++ show i ++ ": " ++ show orig ++ " + " ++ show adj ++ " = " ++ show (orig + adj)

-- | Returns adjoints of the initial job: job ID 0.
{-# NOINLINE dualpass #-}
dualpass :: JobDescr -> JobID -> (d -> BuildState -> IO ()) -> d -> VS.Vector Double
dualpass finaljob (JobID numjobs) backprop adj = unsafePerformIO $ do
  -- hPutStrLn stderr $ "\n-------------------- ENTERING DUALPASS --------------------"
  -- hPutStrLn stderr $ "dualpass: numjobs=" ++ show numjobs
  evlog "dual start"
  -- t1 <- getTime Monotonic
  -- hPutStrLn stderr $ "dual(numjobs=" ++ show numjobs ++ ")"
  threads' <- MV.replicate numjobs Nothing
  allocBS finaljob threads'
  threads <- MV.generateM numjobs (\i ->
                MV.read threads' i >>= \case
                  Just p -> return p
                  Nothing -> error $ "Thread array not initialised: " ++ show i)
  evlog "dual allocated"
  -- t2 <- getTime Monotonic
  -- hPutStrLn stderr $ "prev = " ++ show prev
  -- hPutStrLn stderr $ "iout = " ++ show iout
  -- hPutStrLn stderr $ "adj = " ++ show adj
  backprop adj threads
  -- hPutStrLn stderr $ "-- resolve --"
  evlog "dual bped"
  -- t3 <- getTime Monotonic
  resolve finaljob threads
  evlog "dual resolved"
  -- t4 <- getTime Monotonic
  adjarr0 <- snd <$> MV.read threads 0
  -- hPutStrLn stderr $ "\n//////////////////// FINISHED DUALPASS ////////////////////"
  res <- VS.freeze adjarr0
  evlog "dual frozen"
  -- t5 <- getTime Monotonic
  -- let tms = [t1, t2, t3, t4, t5]
  -- hPutStrLn stderr $ "dual: " ++ intercalate " / " (zipWith (\t t' -> show (fromIntegral (toNanoSecs (diffTimeSpec t t')) / 1e6 :: Double) ++ "ms") tms (tail tms))
  return res


-- ------------------------------------------------------------
-- Structure descriptions of types
-- ------------------------------------------------------------

-- | The structure of a type, as used by the AD transformation. Use
-- 'structureFromTypeable' or 'structureFromType' to construct a 'Structure'.
data Structure = Structure MonoType DataTypes
  deriving (Show)

instance NFData Structure where
  rnf (Structure m ds) = rnf m `seq` rnf (show ds)

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

instance NFData (SimpleType mf) where
  rnf DiscreteST = ()
  rnf ScalarST = ()
  rnf (VarST n) = n `seq` ()
  rnf (ConST n ts) = n `seq` rnf ts

discreteTypeNames :: [Name]
discreteTypeNames =
  [''Int, ''Int8, ''Int16, ''Int32, ''Int64
  ,''Word, ''Word8, ''Word16, ''Word32, ''Word64
  ,''Char, ''Bool]

summariseType :: MonadFail m => Type -> m PolyType
summariseType = \case
  ConT n
    | n `elem` discreteTypeNames
    -> return DiscreteST
    | n == ''Double -> return ScalarST
    | n == ''Float -> fail "Only Double is an active type for now (Float isn't)"
    | otherwise -> return $ ConST n []
  VarT n -> return $ VarST n
  ParensT t -> summariseType t
  TupleT k -> return $ ConST (tupleTypeName k) []
  ListT -> return $ ConST ''[] []
  t@AppT{} -> do
    let (hd, args) = collectApps t
    hd' <- summariseType hd
    args' <- mapM summariseType args
    smartAppsST hd' args'
  t -> fail $ "Unsupported type: " ++ pprint t
  where
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
reverseAD = reverseAD' Nothing (structureFromTypeable (Proxy @a)) (structureFromTypeable (Proxy @b))

reverseAD_tm :: forall a b. (Typeable a, Typeable b)
             => Code Q (IORef Double)
             -> Code Q (a -> b)
             -> Code Q (a -> (b, b -> a))
reverseAD_tm fwdtmref = reverseAD' (Just fwdtmref) (structureFromTypeable (Proxy @a)) (structureFromTypeable (Proxy @b))

-- | Same as 'reverseAD', but with user-supplied 'Structure's.
reverseAD' :: forall a b.
              Maybe (Code Q (IORef Double))
           -> Q Structure  -- ^ Structure of @a@
           -> Q Structure  -- ^ Structure of @b@
           -> Code Q (a -> b)
           -> Code Q (a -> (b, b -> a))
reverseAD' mfwdtmref inpStruc outStruc (unTypeCode -> inputCode) =
  unsafeCodeCoerce $ do
    inpStruc' <- inpStruc
    outStruc' <- outStruc
    ex <- inputCode
    transform mfwdtmref inpStruc' outStruc' ex

transform :: Maybe (Code Q (IORef Double)) -> Structure -> Structure -> TH.Exp -> Q TH.Exp
transform mfwdtmref inpStruc outStruc expr = do
  expr' <- translate expr
  case expr' of
    ELam pat body -> transform' mfwdtmref inpStruc outStruc pat body
    _ -> fail $ "Top-level expression in reverseAD must be lambda, but is: " ++ show expr'

transform' :: Maybe (Code Q (IORef Double)) -> Structure -> Structure -> Pat -> Source.Exp -> Q TH.Exp
transform' mfwdtmref inpStruc outStruc pat expr = do
  _ <- liftIO $ evaluate (force inpStruc)
  _ <- liftIO $ evaluate (force outStruc)
  patbound <- boundVars pat
  argvar <- newName "arg"
  rebuildvar <- newName "rebuild"
  rebuild'var <- newName "rebuild'"
  outvar <- newName "out"
  outjdvar <- newName "outjd"
  outnextjivar <- newName "outnextji"
  primalvar <- newName "primal"
  primal'var <- newName "primal'"
  dualvar <- newName "dual"
  dual'var <- newName "dual'"
  adjvar <- newName "adjoint"
  [| \ $(varP argvar) ->
        let ($(varP outjdvar), $(varP outnextjivar), ($(varP rebuildvar), $(varP primalvar), $(varP dualvar))) =
              runFwdM' $(maybe [| Nothing |] (\c -> [| Just $(unTypeCode c) |]) mfwdtmref) $ do
                ($(pure pat), $(varP rebuild'var)) <- $(interleave inpStruc (VarE argvar))
                $(varP outvar) <- $(ddr patbound expr)
                ($(varP primal'var), $(varP dual'var)) <- mpure $(deinterleave outStruc (VarE outvar))
                liftIO $ debug "evaluate start"
                _ <- return $! $(varE primal'var)
                _ <- return $! $(varE dual'var)
                liftIO $ debug "evaluate done"
                mpure ($(varE rebuild'var), $(varE primal'var), $(varE dual'var))
        in ($(varE primalvar)
           ,\ $(varP adjvar) ->
                $(varE rebuildvar) $! dualpass $(varE outjdvar) $(varE outnextjivar) $(varE dualvar) $(varE adjvar)) |]


-- ----------------------------------------------------------------------
-- The compositional code transformation
-- ----------------------------------------------------------------------

-- "Dual" number
data DN = DN {-# UNPACK #-} !Double
             {-# UNPACK #-} !NID
             !Contrib

-- Set of names bound in the program at this point
type Env = Set Name

-- Γ |- t : a                        -- expression
-- ~> Dt[Γ] |- D[i, t] : FwdM Dt[a]  -- result
ddr :: Env -> Source.Exp -> Q TH.Exp
ddr env = \case
  EVar name
    | name `Set.member` env -> [| mpure $(varE name) |]
    | name == 'fromIntegral -> [| mpure fromIntegralOp |]
    | name == 'negate -> do
        xname <- newName "x"
        [| mpure (\ $(varP xname) -> applyUnaryOp $(varE xname) negate (\_ -> (-1))) |]
    | name == 'sqrt -> do
        xname <- newName "x"
        pname <- newName "p"
        [| mpure (\ $(varP xname) ->
              applyUnaryOp $(varE xname) sqrt (\ $(varP pname) -> 1 / (2 * sqrt $(varE pname)))) |]
    | name == 'exp -> do
        xname <- newName "x"
        primalname <- newName "p"
        [| mpure (\ $(varP xname) ->
              applyUnaryOp2 $(varE xname) exp (\_ $(varP primalname) -> $(varE primalname))) |]
    | name == 'log -> do
        xname <- newName "x"
        pname <- newName "p"
        [| mpure (\ $(varP xname) ->
              applyUnaryOp $(varE xname) log (\ $(varP pname) -> 1 / $(varE pname))) |]
    | name == 'sin -> do
        xname <- newName "x"
        pname <- newName "p"
        [| mpure (\ $(varP xname) ->
              applyUnaryOp $(varE xname) sin (\ $(varP pname) -> cos $(varE pname))) |]
    | name == 'cos -> do
        xname <- newName "x"
        pname <- newName "p"
        [| mpure (\ $(varP xname) ->
              applyUnaryOp $(varE xname) cos (\ $(varP pname) -> - sin $(varE pname))) |]
    | name == '($) -> do
        fname <- newName "f"
        xname <- newName "x"
        ddr env (ELam (VarP fname) $ ELam (VarP xname) $ EVar fname `EApp` EVar xname)
    | name == '(.) -> do
        fname <- newName "f"
        gname <- newName "g"
        xname <- newName "x"
        ddr env (ELam (VarP fname) $ ELam (VarP gname) $ ELam (VarP xname) $ EVar fname `EApp` (EVar gname `EApp` EVar xname))
    | name == '(+) -> ddrNumBinOp '(+) (False, False) (\_ _ -> [| (1, 1) |])
    | name == '(-) -> ddrNumBinOp '(-) (False, False) (\_ _ -> [| (1, -1) |])
    | name == '(*) -> ddrNumBinOp '(*) (True, True) (\x y -> [| ($y, $x) |])
    | name == '(/) -> ddrNumBinOp '(/) (True, True) (\x y -> [| (recip $y, (- $x) / ($y * $y)) |])
    | name `elem` ['(==), '(/=), '(<), '(>), '(<=), '(>=)] -> do
        xname <- newName "x"
        yname <- newName "y"
        [| mpure (\ $(varP xname) ->
             mpure (\ $(varP yname) ->
               mpure (applyCmpOp $(varE xname) $(varE yname)
                                 $(varE name)))) |]
    | name == '(|*|) ->
        fail $ "The parallel combinator (|*|) should be applied directly; partially applying it is pointless."
    | name == 'error -> [| mpure error |]
    | name == 'fst -> [| mpure (\x -> mpure (fst x)) |]
    | name == 'snd -> [| mpure (\x -> mpure (snd x)) |]
    | otherwise -> do
        typ <- reifyType name
        let (params, retty) = unpackFunctionType typ
        if all isDiscrete params && isDiscrete retty
          then [| mpure $(liftKleisliN (length params) (VarE name)) |]
          else fail $ "Most free variables not supported in reverseAD: " ++ show name ++
                      " (env = " ++ show env ++ ")"

  ECon name -> do
    fieldtys <- checkDatacon name
    [| mpure $(liftKleisliN (length fieldtys) (ConE name)) |]

  ELit lit -> case lit of
    RationalL _ -> do
      iname <- newName "i"
      [| do $(varP iname) <- fwdmGenId
            mpure (DN $(litE lit) $(varE iname) C0) |]
    FloatPrimL _ -> fail "float prim?"
    DoublePrimL _ -> fail "double prim?"
    IntegerL _ -> [| mpure $(litE lit) |]
    StringL _ -> [| mpure $(litE lit) |]
    _ -> fail $ "literal? " ++ show lit

  EVar name `EApp` e1 `EApp` e2 | name == '(|*|) ->
    [| fwdmPar $(ddr env e1) $(ddr env e2) |]

  EApp e1 e2 -> do
    (wrap, [funname, argname]) <- ddrList env [e1, e2]
    return (wrap (VarE funname `AppE` VarE argname))

  ELam pat e -> do
    patbound <- boundVars pat
    e' <- ddr (env <> patbound) e
    [| mpure (\ $(pure pat) -> $(pure e')) |]

  ETup es -> do
    (wrap, vars) <- ddrList env es
    return (wrap $ VarE 'mpure `AppE` TupE (map (Just . VarE) vars))

  ECond e1 e2 e3 -> do
    e1' <- ddr env e1
    boolName <- newName "bool"
    e2' <- ddr env e2
    e3' <- ddr env e3
    return (DoE Nothing
              [BindS (VarP boolName) e1'
              ,NoBindS (CondE (VarE boolName) e2' e3')])

  ELet decs body -> do
    (wrap, vars) <- ddrDecs env decs
    body' <- ddr (env <> Set.fromList vars) body
    return $ wrap body'

  ECase expr matches -> do
    (wrap, [evar]) <- ddrList env [expr]
    matches' <- sequence
      [do patbound <- boundVars pat
          ddrPat pat
          (pat,) <$> ddr (env <> patbound) rhs
      | (pat, rhs) <- matches]
    return $ wrap $
      CaseE (VarE evar)
        [Match pat (NormalB rhs) [] | (pat, rhs) <- matches']

  EList es -> do
    (wrap, vars) <- ddrList env es
    return (wrap (VarE 'mpure `AppE` ListE (map VarE vars)))

  ESig e ty ->
    [| $(ddr env e) :: FwdM $(ddrType ty) |]

ddrNumBinOp :: Name  -- ^ Primal operator
            -> (Bool, Bool)  -- ^ Whether the gradient uses its (first, second) argument
            -> (Q TH.Exp -> Q TH.Exp -> Q TH.Exp)
                  -- ^ Gradient given inputs (assuming adjoint 1).
                  -- Should return a pair: the partial derivaties with respect
                  -- to the two inputs. The names are variable references for
                  -- the two primal inputs.
            -> Q TH.Exp
ddrNumBinOp op (xused, yused) mkgrad = do
  xname <- newName "x"
  yname <- newName "y"
  pxname <- newName "px"
  pyname <- newName "py"
  [| mpure (\ $(varP xname) ->
       mpure (\ $(varP yname) ->
         applyBinaryOp $(varE xname) $(varE yname)
                       $(varE op)
                       (\ $(if xused then varP pxname else wildP)
                          $(if yused then varP pyname else wildP) ->
                            $(mkgrad (varE pxname) (varE pyname))))) |]

-- | Given list of expressions, returns a wrapper that defines a variable for
-- each item in the list (differentiated), together with a list of the names of
-- those variables.
-- The expressions must all have the same, given, environment.
ddrList :: Env -> [Source.Exp] -> Q (TH.Exp -> TH.Exp, [Name])
ddrList env es = do
  names <- mapM (\idx -> newName ("x" ++ show idx)) [1 .. length es]
  rhss <- mapM (ddr env) es
  return (\rest ->
            DoE Nothing $ [BindS (VarP nx) e | (nx, e) <- zip names rhss] ++ [NoBindS rest]
         ,names)

-- | Assumes the declarations occur in a let block.
-- Returns:
-- * a wrapper that defines all of the names;
-- * the list of defined names.
ddrDecs :: Env -> [DecGroup] -> Q (TH.Exp -> TH.Exp, [Name])
ddrDecs env decs = do
  let ddrDecGroups _ [] = return ([], [])
      ddrDecGroups env' (g : gs) = do
        (stmt, bound) <- ddrDecGroup env' g
        (rest, restbound) <- ddrDecGroups (env' <> Set.fromList bound) gs
        return (stmt : rest, bound ++ restbound)

  (stmts, declared) <- ddrDecGroups env decs

  return
    (\body -> DoE Nothing $ stmts ++ [NoBindS body]
    ,declared)

ddrDecGroup :: Env -> DecGroup -> Q (Stmt, [Name])
ddrDecGroup env (DecVar name msig rhs) = do
  rhs' <- ddr env rhs
  rhs'' <- case msig of Just sig -> do sig' <- ddrType sig
                                       return $ SigE rhs' (AppT (ConT ''FwdM) sig')
                        Nothing -> return rhs'
  return (BindS (VarP name) rhs'', [name])
ddrDecGroup env (DecMutGroup lams) = do
  let names = [name | (name, _, _, _) <- lams]
  decs <- concat <$> sequence
    [do ddrPat pat
        bound <- boundVars pat
        rhs' <- ddr (env <> Set.fromList names <> bound) rhs
        let dec = ValD (VarP name) (NormalB (LamE [pat] rhs')) []
        case msig of
          Just sig -> do sig' <- ddrType sig
                         return [SigD name sig', dec]
          Nothing -> return [dec]
    | (name, msig, pat, rhs) <- lams]
  return (LetS decs, names)

-- | Only checks that the data constructors appearing in the pattern are of
-- supported types.
ddrPat :: Pat -> Q ()
ddrPat = \case
  LitP{} -> fail "Literals in patterns unsupported"
  VarP{} -> return ()
  TupP ps -> mapM_ ddrPat ps
  UnboxedTupP ps -> mapM_ ddrPat ps
  p@UnboxedSumP{} -> notSupported "Unboxed sums" (Just (show p))
  p@(ConP name tyapps args)
    | not (null tyapps) -> notSupported "Type applications in patterns" (Just (show p))
    -- | name `elem` ['(:), '[]] -> mapM_ ddrPat args  -- TODO unnecessary special cases?
    | otherwise -> do
        -- ignore the field types; just validity is good enough, assuming that the user's code was okay
        _ <- checkDatacon name
        mapM_ ddrPat args
  InfixP p1 name p2 -> ddrPat (ConP name [] [p1, p2])
  p@UInfixP{} -> notSupported "UInfix patterns" (Just (show p))
  ParensP p -> ddrPat p
  p@TildeP{} -> notSupported "Irrefutable patterns" (Just (show p))
  p@BangP{} -> notSupported "Bang patterns" (Just (show p))
  AsP _ p -> ddrPat p
  WildP -> return ()
  p@RecP{} -> notSupported "Records" (Just (show p))
  ListP ps -> mapM_ ddrPat ps
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
      | name == ''Double = Right (ConT ''DN)
      | name == ''Int = Right (ConT ''Int)
    go (ArrowT `AppT` t1 `AppT` t) = do
      t1' <- go t1
      t' <- go t
      return $ ArrowT `AppT` t1' `AppT` (ConT ''FwdM `AppT` t')
    go (MulArrowT `AppT` PromotedT multi `AppT` t1 `AppT` t)
      | multi == 'Many = go (ArrowT `AppT` t1 `AppT` t)
    go ty =
      case collectApps ty of
        (TupleT n, args) | length args == n ->
          foldl AppT (TupleT n) <$> traverse go args
        (ConT name, args) ->  -- I hope this one is correct
          foldl AppT (ConT name) <$> traverse go args
        _ -> Left ty  -- don't know how to handle this type


-- ----------------------------------------------------------------------
-- The wrapper: interleave and deinterleave
-- ----------------------------------------------------------------------

-- input :: a
-- result :: FwdM (Dt[a], VS.Vector Double -> a)
interleave :: Quote m => Structure -> TH.Exp -> m TH.Exp
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
-- 'T -> (Dt[T], VS.Vector Double -> T)'. The Map contains for each
-- (type name T', type arguments As') combination that occurs (transitively) in
-- T, the name of a function with type
-- 'T' As' -> (Dt[T' As'], VS.Vector Double -> T' As')'.
interleaveData :: Quote m => Map (Name, [MonoType]) Name -> [(Name, [MonoType])] -> m TH.Exp
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
        --      mpure (C post₁ post₂ post₃
        --            ,\arr -> C (rebuild₁ arr) (rebuild₂ arr) (rebuild₃ arr))
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
          [NoBindS $ VarE 'mpure `AppE`
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
-- 'T' As' -> FwdM (Dt[T' As'], VS.Vector Double -> T' As')'.
interleaveType :: Quote m => Map (Name, [MonoType]) Name -> MonoType -> m TH.Exp
interleaveType helpernames = \case
  DiscreteST -> do
    inpxvar <- newName "inpx"
    [| \ $(varP inpxvar) -> mpure ($(varE inpxvar), \_ -> $(varE inpxvar)) |]

  ScalarST -> do
    inpxvar <- newName "inpx"
    ivar <- newName "i"
    arrvar <- newName "arr"
    [| \ $(varP inpxvar) -> do
           $(varP ivar) <- fwdmGenIdInterleave
           mpure (DN $(varE inpxvar) (NID (JobID 0) $(varE ivar)) C0
                 ,\ $(varP arrvar) -> $(varE arrvar) VS.! $(varE ivar)) |]

  ConST tyname argtys ->
    return $ VarE $ case Map.lookup (tyname, argtys) helpernames of
                      Just name -> name
                      Nothing -> error $ "Helper name not defined? " ++ show (tyname, argtys)

-- outexp :: Dt[T]                       -- interleaved program output
-- result :: (T                          -- primal result
--           ,T -> BuildState -> IO ())  -- given adjoint, add initial contributions
deinterleave :: Quote m => Structure -> TH.Exp -> m TH.Exp
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

-- Dt[T]                            -- interleaved program output
--   -> (T                          -- primal result
--      ,T -> BuildState -> IO ())  -- given adjoint, add initial contributions
-- The Map contains for each (type name T', type arguments As') combination
-- that occurs (transitively) in T, the name of a function with type
-- 'Dt[T' As'] -> (T' As', T' As' -> BuildState -> IO ())'.
deinterleaveData :: Quote m => Map (Name, [MonoType]) Name -> [(Name, [MonoType])] -> m TH.Exp
deinterleaveData helpernames constrs = do
  dualvar <- newName "out"
  let maxn = maximum (map (length . snd) constrs)
  alldvars <- mapM (\i -> newName ("d" ++ show i)) [1..maxn]
  allpvars <- mapM (\i -> newName ("p" ++ show i)) [1..maxn]
  allfvars <- mapM (\i -> newName ("f" ++ show i)) [1..maxn]
  allavars <- mapM (\i -> newName ("a" ++ show i)) [1..maxn]

  bsvar <- newName "bs"

  let composeActions [] = LamE [WildP] (VarE 'return `AppE` TupE [])
      composeActions l =
        LamE [VarP bsvar] $
          foldr1 (\a b -> InfixE (Just a) (VarE '(>>)) (Just b))
                 (map (`AppE` VarE bsvar) l)

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
                           -- TODO: is this type signature still necessary now that we've moved
                           -- away from linear types?
                           SigE (composeActions [VarE fvar `AppE` VarE avar
                                                | (fvar, avar) <- zip fvars avars])
                                (MulArrowT `AppT` ConT 'Many `AppT` ConT ''BuildState `AppT` (ConT ''IO `AppT` TupleT 0)))
    | (conname, fieldtys) <- constrs]

  return $ LamE [VarP dualvar] $ CaseE (VarE dualvar)
    [Match (ConP conname [] (map VarP dvars))
           (NormalB body)
           []
    | ((conname, fieldtys), body) <- zip constrs bodies
    , let dvars = take (length fieldtys) alldvars]

-- Dt[T]                            -- interleaved program output
--   -> (T                          -- primal result
--      ,T -> BuildState -> IO ())  -- given adjoint, add initial contributions
-- The Map contains for each (type name T', type arguments As') combination
-- that occurs (transitively) in T, the name of a function with type
-- 'Dt[T' As'] -> (T' As', T' As' -> BuildState -> IO ())'.
deinterleaveType :: Quote m => Map (Name, [MonoType]) Name -> MonoType -> m TH.Exp
deinterleaveType helpernames = \case
  DiscreteST -> do
    dname <- newName "d"
    [| \ $(varP dname) -> ($(varE dname), \_ _ -> return () :: IO ()) |]

  ScalarST -> do
    primalname <- newName "prim"
    idname <- newName "id"
    cbname <- newName "cb"
    return $ LamE [ConP 'DN [] [VarP primalname, VarP idname, VarP cbname]] $
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
  type DualNum Double = DN
  applyBinaryOp (DN x xi xcb) (DN y yi ycb) primal grad = do
    let (dx, dy) = grad x y
    i <- fwdmGenId
    pure (DN (primal x y) i (C2 (CEdge xi xcb dx) (CEdge yi ycb dy)))
  applyUnaryOp (DN x xi xcb) primal grad = do
    i <- fwdmGenId
    pure (DN (primal x) i (C1 (CEdge xi xcb (grad x))))
  applyUnaryOp2 (DN x xi xcb) primal grad = do
    i <- fwdmGenId
    let pr = primal x
    pure (DN pr i (C1 (CEdge xi xcb (grad x pr))))
  applyCmpOp (DN x _ _) (DN y _ _) f = f x y
  fromIntegralOp x = do
    i <- fwdmGenId
    pure (DN (fromIntegral x) i C0)

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

-- | Only unpacks normal function arrows, not linear ones.
unpackFunctionType :: Type -> ([Type], Type)
unpackFunctionType (ArrowT `AppT` ty `AppT` t) = first (ty :) (unpackFunctionType t)
unpackFunctionType (MulArrowT `AppT` PromotedT multi `AppT` ty `AppT` t)
  | multi == 'Many = first (ty :) (unpackFunctionType t)
unpackFunctionType t = ([], t)

isDiscrete :: Type -> Bool
isDiscrete (ConT n) = n `elem` discreteTypeNames
isDiscrete t@AppT{} =
  let (hd, args) = collectApps t
  in case hd of
       TupleT n | length args == n -> all isDiscrete args
       ListT | [arg] <- args -> isDiscrete arg
       _ -> False
isDiscrete _ = False

collectApps :: Type -> (Type, [Type])
collectApps = \t -> go t []
  where
    go (AppT t1 t2) prefix = go t1 (t2 : prefix)
    go t prefix = (t, prefix)

-- | Given an expression `e`, wraps it in `n` kleisli-lifted lambdas like
--
-- > \x1 -> pure (\x2 -> pure (... \xn -> pure (e x1 ... xn)))
liftKleisliN :: Int -> TH.Exp -> Q TH.Exp
liftKleisliN 0 e = return e
liftKleisliN n e = do
  name <- newName "x"
  [| \ $(varP name) -> mpure $(liftKleisliN (n - 1) (e `AppE` VarE name)) |]

pair :: TH.Exp -> TH.Exp -> TH.Exp
pair e1 e2 = TupE [Just e1, Just e2]

tvbName :: TyVarBndr () -> Name
tvbName (PlainTV n _) = n
tvbName (KindedTV n _ _) = n

mapUnionsWithKey :: (Foldable f, Ord k) => (k -> a -> a -> a) -> f (Map k a) -> Map k a
mapUnionsWithKey f = foldr (Map.unionWithKey f) mempty

kENABLE_EVLOG :: Bool
kENABLE_EVLOG = False

evlog :: String -> IO ()
evlog _ | not kENABLE_EVLOG = return ()
evlog s = do
  clk <- getTime Monotonic
  withMVar evlogfile $ \f -> do
    BS.hPut f $ BS8.pack (show (fromIntegral (toNanoSecs clk) / 1e9 :: Double) ++ ' ' : s ++ "\n")
    hFlush f

{-# NOINLINE evlogfile #-}
evlogfile :: MVar Handle
evlogfile = unsafePerformIO $ newMVar =<< openFile "evlogfile.txt" AppendMode
