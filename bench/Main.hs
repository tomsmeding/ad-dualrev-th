{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
module Main where

import Control.DeepSeq (NFData, deepseq)
import Control.Monad (when)
import Criterion
import qualified Criterion.Main as Criterion
import qualified Criterion.Main.Options as Criterion
import GHC.Generics (Generic)
import System.Environment (getArgs)
import System.Exit (die, exitSuccess, exitFailure)

import DFunction
import Language.Haskell.TH.Stupid
import Test.Approx
import Test.Framework hiding (scale)
import Criterion.Types (Config(..))


newtype FMult s = MkFMult (s, s)
  deriving (Show, Functor, Foldable, Traversable)
  deriving (Approx, Arbitrary, NFData) via (s, s)
fmult :: DFunction FMult
fmult = $$(makeFunction (parseType "FMult Double")
  [|| \arg -> case arg of MkFMult (x, y) -> x * y ||])

newtype FDotProd s = FDotProd ([s], [s])
  deriving (Show, Functor, Foldable, Traversable)
  deriving (Approx, Arbitrary, NFData) via ([s], [s])
fdotprod :: DFunction FDotProd
fdotprod = $$(makeFunction (parseType "FDotProd Double")
  [|| \(FDotProd (l1, l2)) ->
        let zipWith' f (x:xs) (y:ys) = f x y : zipWith' f xs ys
            zipWith' _ _ _ = []
            sum' [] = 0.0
            sum' (x:xs) = x + sum' xs
        in sum' (zipWith' (\x y -> x * y) l1 l2) ||])

newtype FSumMatVec s = FSumMatVec ([[s]], [s])
  deriving (Show, Functor, Foldable, Traversable)
  deriving (Approx, Arbitrary, NFData) via ([[s]], [s])
fsummatvec :: DFunction FSumMatVec
fsummatvec = $$(makeFunction (parseType "FSumMatVec Double")
  [|| \(FSumMatVec (m, v)) ->
        let zipWith' f (x:xs) (y:ys) = f x y : zipWith' f xs ys
            zipWith' _ _ _ = []
            sum' [] = 0.0
            sum' (x:xs) = x + sum' xs
            dotp v1 v2 = sum' (zipWith' (\x y -> x * y) v1 v2)
            map' _ [] = []
            map' f (x:xs) = f x : map' f xs
        in sum' (map' (dotp v) m) ||])

data Vec3 s = Vec3 s s s
  deriving (Show, Functor, Foldable, Traversable, Generic)
data Quaternion s = Quaternion s s s s
  deriving (Show, Functor, Foldable, Traversable, Generic)
newtype FRotVecQuat s = FRotVecQuat (Vec3 s, Quaternion s)
  deriving (Show, Functor, Foldable, Traversable)
  deriving (Approx, Arbitrary, NFData) via (Vec3 s, Quaternion s)

instance NFData s => NFData (Vec3 s)
instance NFData s => NFData (Quaternion s)

instance Arbitrary s => Arbitrary (Vec3 s) where arbitrary = Vec3 <$> arbitrary <*> arbitrary <*> arbitrary
instance Arbitrary s => Arbitrary (Quaternion s) where arbitrary = Quaternion <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary

instance Approx s => Approx (Vec3 s) where
  approx absdelta reldelta (Vec3 a b c) (Vec3 a' b' c') = approx absdelta reldelta [a,b,c] [a',b',c']
instance Approx s => Approx (Quaternion s) where
  approx absdelta reldelta (Quaternion a b c d) (Quaternion a' b' c' d') = approx absdelta reldelta [a,b,c,d] [a',b',c',d']

-- The example function from [Krawiec et al. 2022], with the output vector
-- summed in order to return a 'Double'.
frotvecquat :: DFunction FRotVecQuat
frotvecquat = $$(makeFunction (parseType "FRotVecQuat Double")
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
        in (\(Vec3 x y z) -> x + y + z) $ rotate_vec_by_quat topv topq ||])

data Options = Options
  { argsPatternsRev :: [String]
  , argsOutput :: Maybe FilePath
  , argsHelp :: Bool }
  deriving (Show)

parseArgs :: [String] -> Options -> Either String Options
parseArgs [] a = return a
parseArgs ("-o" : path : ss) a = parseArgs ss (a { argsOutput = Just path })
parseArgs ("-h" : _) a = return $ a { argsHelp = True }
parseArgs ("--help" : _) a = return $ a { argsHelp = True }
parseArgs ("" : _) _ = Left "Unexpected empty argument"
parseArgs (s@(c0:_) : ss) a
  | c0 /= '-' = parseArgs ss (a { argsPatternsRev = s : argsPatternsRev a })
parseArgs (s : _) _ = Left ("Unrecognised argument '" ++ s ++ "'")

main :: IO ()
main = do
  options <- getArgs >>= \args -> case parseArgs args (Options [] Nothing False) of
               Left err -> die err
               Right opts -> return opts

  when (argsHelp options) $ do
    putStrLn "Usage: bench [-o <criterion-output.html>] [test patterns...]"
    exitSuccess

  checksOK <- runTestsPatterns (reverse (argsPatternsRev options)) $
    tree "correctness"
      [changeArgs (\args -> args { maxSuccess = 50000 }) $
       tree "fast"
         [property "fmult" (\x -> radWithTH fmult x ~= radWithAD fmult x)
         ,property "fdotprod" (\x -> radWithTH fdotprod x ~= radWithAD fdotprod x)
         ,property "frotvecquat" (\x -> radWithTH frotvecquat x ~= radWithAD frotvecquat x)]
      ,changeArgs (\args -> args { maxSuccess = 5000 }) $
       tree "slow"
         [property "fsummatvec" (\x -> radWithTH fsummatvec x ~= radWithAD fsummatvec x)]]

  when (not checksOK) exitFailure

  let crconfig = Criterion.defaultConfig { reportFile = argsOutput options }
  Criterion.runMode
    (Criterion.Run crconfig Criterion.Pattern (reverse (argsPatternsRev options)))
    [bgroup "fmult"
      [bench "TH" (nf (radWithTH fmult) (MkFMult (3.0, 4.0)))
      ,bench "ad" (nf (radWithAD fmult) (MkFMult (3.0, 4.0)))]
    ,bgroup "fdotprod" $
      let run f n =
            let l1 = take (fromIntegral n) [1..]
                l2 = take (fromIntegral n) [3,5..]
            in f fdotprod (FDotProd (l1, l2)) `deepseq` return ()
      in [bench "TH" (toBenchmarkable (run radWithTH))
         ,bench "ad" (toBenchmarkable (run radWithAD))]
    ,bgroup "fsummatvec" $
      let run f n2 =
            let n = round (sqrt (fromIntegral n2 :: Double))
                l1 = take n (blockN n [1..])
                l2 = take n [3,5..]
            in f fsummatvec (FSumMatVec (l1, l2)) `deepseq` return ()
      in [bench "TH" (toBenchmarkable (run radWithTH))
         ,bench "ad" (toBenchmarkable (run radWithAD))]
    ,bgroup "frotvecquat" $
      [bench "TH" (nf (radWithTH frotvecquat) (FRotVecQuat (Vec3 1 2 3, Quaternion 4 5 6 7)))
      ,bench "ad" (nf (radWithAD frotvecquat) (FRotVecQuat (Vec3 1 2 3, Quaternion 4 5 6 7)))]
    ]
  where
    blockN :: Int -> [a] -> [[a]]
    blockN _ [] = []
    blockN n l = let (pre, post) = splitAt n l in pre : blockN n post
