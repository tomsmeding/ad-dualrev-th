{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
module Main where

import Control.Concurrent
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad
import Criterion
import Criterion.Types (Config(..))
import qualified Criterion.Main as Criterion
import qualified Criterion.Main.Options as Criterion
import Data.Functor.Identity
import System.Clock
import System.Environment (getArgs)
import System.Exit (die, exitSuccess, exitFailure)
import System.Mem (performGC)
import System.IO

import Control.Concurrent.ThreadPool
import DFunction
import Language.Haskell.ReverseAD.TH ((|*|), evlog, reverseAD)
import Test.Approx
import Test.Framework hiding (scale)
import Types


fmult :: DFunction FMult Identity
fmult = $$(makeFunction
  [|| \arg -> Identity $ case arg of MkFMult (x, y) -> x * y ||])

fdotprod :: DFunction FDotProd Identity
fdotprod = $$(makeFunction
  [|| \(FDotProd (l1, l2)) ->
        let zipWith' f (x:xs) (y:ys) = f x y : zipWith' f xs ys
            zipWith' _ _ _ = []
            sum' [] = 0.0
            sum' (x:xs) = x + sum' xs
        in Identity $ sum' (zipWith' (\x y -> x * y) l1 l2) ||])

fsummatvec :: DFunction FSumMatVec Identity
fsummatvec = $$(makeFunction
  [|| \(FSumMatVec (m, v)) ->
        let zipWith' f (x:xs) (y:ys) = f x y : zipWith' f xs ys
            zipWith' _ _ _ = []
            sum' [] = 0.0
            sum' (x:xs) = x + sum' xs
            dotp v1 v2 = sum' (zipWith' (\x y -> x * y) v1 v2)
            map' _ [] = []
            map' f (x:xs) = f x : map' f xs
        in Identity $ sum' (map' (dotp v) m) ||])

-- The example function from [Krawiec et al. 2022].
frotvecquat :: DFunction FRotVecQuat Vec3
frotvecquat = $$(makeFunction
  [|| \(FRotVecQuat (topv, topq)) ->
        let q_to_vec (Quaternion x y z _) = Vec3 x y z
            dot (Vec3 px py pz) (Vec3 qx qy qz) = px * qx + py * qy + pz * qz
            vadd (Vec3 px py pz) (Vec3 qx qy qz) = Vec3 (px + qx) (py + qy) (pz + qz)
            scale k (Vec3 x y z) = Vec3 (k * x) (k * y) (k * z)
            cross (Vec3 ax ay az) (Vec3 bx by bz) = Vec3 (ay*bz - az*by) (az*bz - ax*bz) (ax*by - ay*bx)
            -- norm x = sqrt (dot x x)  -- present in code in paper, but unused
            rotate_vec_by_quat v q =
              let u = q_to_vec q
                  s = case q of Quaternion _ _ _ w -> w
              in scale (2.0 * dot u v) u `vadd` scale (s * s - dot u u) v `vadd` scale (2.0 * s) (cross u v)
        in rotate_vec_by_quat topv topq ||])

fparticles_gen :: Int -> DFunction FParticles Identity
fparticles_gen iters = $$(makeFunction
  [|| \(FParticles l) ->
        let parmap _ [] = []
            parmap f (x:xs) =
              let (y, ys) = f x |*| parmap f xs
              in y : ys
            (a, b) .+ (c, d) = (a + c, b + d)
            s .* (a, b) = (s * a, s * b)
            forceField p = (-0.5) .* p
            friction v = (-0.2) .* v
            mass = 1.0
            -- step :: (Double, Double) -> (Double, Double) -> Double
            --      -> ((Double, Double), (Double, Double))
            step p v dt =
              let a = (1.0 / mass) .* (forceField p .+ friction v)
              in (p .+ (dt .* v), v .+ (dt .* a))
            -- loop :: Int -> (Double, Double) -> (Double, Double) -> (Double, Double)
            loop n p v =
              if n == (0 :: Int) then p
                else let (p', v') = step p v 0.05
                     in loop (n-1) p' v'
            sum' [] = 0.0
            sum' ((x,y):xs) = x*y + sum' xs
        in Identity $ sum' (parmap (\(p, v) -> loop iters p v) l) ||])

fparticles :: DFunction FParticles Identity
fparticles = fparticles_gen 1000

{-# NOINLINE fparticles_gen_ad #-}
fparticles_gen_ad :: Int -> [((Double, Double), (Double, Double))] -> (Double, Double -> [((Double, Double), (Double, Double))])
fparticles_gen_ad iters = $$(reverseAD
  [|| \l ->
        let parmap _ [] = []
            parmap f (x:xs) =
              let (y, ys) = f x |*| parmap f xs
              in y : ys
            (a, b) .+ (c, d) = (a + c, b + d)
            s .* (a, b) = (s * a, s * b)
            forceField p = (-0.5) .* p
            friction v = (-0.2) .* v
            mass = 1.0
            step :: (Double, Double) -> (Double, Double) -> Double
                 -> ((Double, Double), (Double, Double))
            step p v dt =
              let a = (1.0 / mass) .* (forceField p .+ friction v)
              in (p .+ (dt .* v), v .+ (dt .* a))
            -- isum :: Int -> Int -> Int
            -- isum n k = if n == 0 then k else isum (n - 1) (k * k + k)
            loop :: Int -> {- Int -> -} (Double, Double) -> (Double, Double) -> (Double, Double)
            loop n {- k -} p v =
              if n == (0 :: Int) then p
                else let (p', v') = step p v 0.05
                     in loop (n-1) {- (isum 50 k) -} p' v'
            sum' [] = 0.0
            sum' ((x,y):xs) = x*y + sum' xs
        in sum' (parmap (\(p, v) -> loop iters {- 0 -} p v) l) ||])

runParTest :: IO ()
runParTest = do
  getNumCapabilities >>= \num -> hPutStrLn stderr ("Using " ++ show num ++ " threads")
  let input = [((fromIntegral i * 0.5, 0.1), (1.0, 1.0)) | i <- [1..4::Int]]
  forM_ [500, 1000 .. 10000] $ \iters -> do
  -- forM_ [10000, 20000 .. 100000] $ \iters -> do
  -- forM_ [70000] $ \iters -> do
    _ <- func iters input 0
    (tottms, ptms, dtms) <- unzip3 <$> forM [1..10] (func iters input)
    -- print (ptms, dtms)
    putStrLn $ show iters ++ " " ++ show (average tottms) ++ " " ++ show (average ptms) ++ " " ++ show (average dtms)
    hFlush stdout
  where
    {-# NOINLINE func #-}
    func :: Int -> [((Double, Double), (Double, Double))] -> Int -> IO (Double, Double, Double)
    func iters input _ = do
      performGC
      -- hPutStrLn stderr "=== func ==="
      (tmtot, (tm1, tm2)) <- timed $ do
        let (primal, dual) = fparticles_gen_ad iters input
        (tm1, _) <- timed $ evaluate (primal :: Double)
        (tm2, _) <- timed $ evaluate (force (dual 1.0))
        return (tm1, tm2)
      return (tmtot, tm1, tm2)

    {-# NOINLINE timed #-}
    timed :: IO a -> IO (Double, a)
    timed act = do
      evlog "bench start"
      t1 <- getTime Monotonic
      res <- act
      evlog "bench end"
      t2 <- getTime Monotonic
      return (fromIntegral (toNanoSecs (diffTimeSpec t1 t2)) / 1e9, res)

    average l = sum l / fromIntegral (length l)

data Options = Options
  { argsHelp :: Bool
  , argsOutput :: Maybe FilePath
  , argsCsv :: Maybe FilePath
  , argsNoTest :: Bool
  , argsNoBench :: Bool
  , argsPatternsRev :: [String]
  , argsParTest :: Bool }
  deriving (Show)

parseArgs :: [String] -> Options -> Either String Options
parseArgs [] a = return a
parseArgs ("-h" : _) a = return $ a { argsHelp = True }
parseArgs ("--help" : _) a = return $ a { argsHelp = True }
parseArgs ("-o" : path : ss) a = parseArgs ss (a { argsOutput = Just path })
parseArgs ("--notest" : ss) a = parseArgs ss (a { argsNoTest = True })
parseArgs ("--nobench" : ss) a = parseArgs ss (a { argsNoBench = True })
parseArgs ("--csv" : path : ss) a = parseArgs ss (a { argsCsv = Just path })
parseArgs ("--partest" : ss) a = parseArgs ss (a { argsParTest = True })
parseArgs ("" : _) _ = Left "Unexpected empty argument"
parseArgs (s@(c0:_) : ss) a
  | c0 /= '-' = parseArgs ss (a { argsPatternsRev = s : argsPatternsRev a })
parseArgs (s : _) _ = Left ("Unrecognised argument '" ++ s ++ "'")

main :: IO ()
main = do
  options <- getArgs >>= \args -> case parseArgs args (Options False Nothing Nothing False False [] False) of
               Left err -> die err
               Right opts -> return opts

  when (argsHelp options) $ do
    putStrLn "Usage: bench [-o <criterion-output.html>] [--notest] [--csv <results.csv>]\n\
             \             [test patterns...]"
    exitSuccess

  when (argsParTest options) $ do
    runParTest
    exitSuccess

  when (not (argsNoTest options)) $ do
    checksOK <- runTestsPatterns (reverse (argsPatternsRev options)) $
      changeArgs (\args -> args { maxSuccess = 50000 }) $
      tree "correctness"
        [property "fmult" (\x -> radWithTH fmult x ~= radWithAD fmult x)
        ,property "fdotprod" (\x -> radWithTH fdotprod x ~= radWithAD fdotprod x)
        ,property "frotvecquat" (\x -> radWithTH frotvecquat x ~= radWithAD frotvecquat x)
        ,changeArgs (\args -> args { maxSuccess = 5000 }) $
           property "fsummatvec" (\x -> radWithTH fsummatvec x ~= radWithAD fsummatvec x)
        ,changeArgs (\args -> args { maxSuccess = 50 }) $
           property "fparticles" (\x -> radWithTH fparticles x ~= radWithAD fparticles x)]

    when (not checksOK) exitFailure

  when (argsNoBench options) $
    exitSuccess

  let crconfig = Criterion.defaultConfig { reportFile = argsOutput options
                                         , csvFile = argsCsv options }
  Criterion.runMode
    (Criterion.Run crconfig Criterion.Pattern (reverse (argsPatternsRev options)))
    [bgroup "fmult" $
      let input = MkFMult (3.0, 4.0) in
      [bench "TH" (nf (radWithTH fmult) input)
      ,bench "ad" (nf (radWithAD fmult) input)]
    ,bgroup "fdotprod" $
      let run f n =
            let l1 = take (fromIntegral n) [1..]
                l2 = take (fromIntegral n) [3,5..]
            in evaluate (force (f fdotprod (FDotProd (l1, l2)))) >> return ()
      in [bench "TH" (toBenchmarkable (run radWithTH))
         ,bench "ad" (toBenchmarkable (run radWithAD))]
    ,bgroup "fsummatvec" $
      let run f n2 =
            let n = round (sqrt (fromIntegral n2 :: Double))
                l1 = take n (blockN n [1..])
                l2 = take n [3,5..]
            in evaluate (force (f fsummatvec (FSumMatVec (l1, l2)))) >> return ()
      in [bench "TH" (toBenchmarkable (run radWithTH))
         ,bench "ad" (toBenchmarkable (run radWithAD))]
    ,bgroup "frotvecquat" $
      let input = FRotVecQuat (Vec3 1 2 3, Quaternion 4 5 6 7) in
      [bench "TH" (nf (radWithTH frotvecquat) input)
      ,bench "ad" (nf (radWithAD frotvecquat) input)]
    ,bgroup "fparticles" $
      let input = FParticles [((fromIntegral i * 0.5, 0.1), (1.0, 1.0)) | i <- [1..4::Int]] in
      [bgroup "TH"
        [envNumCapabilities 1 $ bench "N1" (nf (radWithTH fparticles) input)
        ,envNumCapabilities 2 $ bench "N2" (nf (radWithTH fparticles) input)
        ,envNumCapabilities 4 $ bench "N4" (nf (radWithTH fparticles) input)]
      ,bgroup "ad"
        [envNumCapabilities 1 $ bench "N1" (nf (radWithAD fparticles) input)
        ,envNumCapabilities 2 $ bench "N2" (nf (radWithAD fparticles) input)
        ,envNumCapabilities 4 $ bench "N4" (nf (radWithAD fparticles) input)]
      ]
    ]
  where
    blockN :: Int -> [a] -> [[a]]
    blockN _ [] = []
    blockN n l = let (pre, post) = splitAt n l in pre : blockN n post

envNumCapabilities :: Int -> Benchmark -> Benchmark
envNumCapabilities n bm =
  envWithCleanup
    (do cur <- getNumCapabilities
        setNumCapabilities n
        scalePool globalThreadPool n
        return cur)
    (\prev -> do
        setNumCapabilities prev
        scalePool globalThreadPool prev)
    (\_ -> bm)
