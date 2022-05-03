{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Main where

import Prelude hiding ((^))
import qualified Prelude

import Data.Monoid (Sum(..))
import Data.Proxy
import Data.Type.Equality

import ControlFun
import FinDiff
import ForwardAD
import Language.Haskell.TH.Stupid
import Test.Approx
import Test.Framework hiding (elements)


(^) :: Num a => a -> Int -> a
(^) = (Prelude.^)


checkControl :: (Arbitrary a, Arbitrary b, Approx a, Approx b, Show a, Show b)
             => String -> (a -> (b, b -> a)) -> (a -> b) -> (a -> b -> a) -> Tree
checkControl name program controlfun controlgrad =
  property name $ \x adj ->
    let (y1, df1) = program x
    in y1 ~= controlfun x && df1 adj ~= controlgrad x adj

data DoCheckFinDiff = YesFD | NoFD
  deriving (Show)

checkFDcontrol :: forall a b.
                  (Arbitrary a, Arbitrary b, Approx a, Approx b, Show a, Show b
                  ,FinDiff a, FinDiff b, Element a ~ Double, Element b ~ Double)
               => String
               -> (a -> (b, b -> a), ControlFun a b)
               -> Maybe (a -> b -> a)
               -> DoCheckFinDiff
               -> Tree
checkFDcontrol name (program, ControlFun controlfun) mcontrolgrad dofindiff
  | Refl <- replaceElementsId @a
  , Refl <- replaceElementsId @b
  = property name $ \x ->
      let refout = controlfun @Double x
          controlJac = (\df -> jacobianByRows refout df x) <$> mcontrolgrad
          programJac = jacobianByRows refout (snd . program) x
          findiffJac = jacobianByFinDiff refout (controlfun @Double) x
          forwardJac = jacobianByCols
                          (\input tangent ->
                              rebuild @b (Proxy @Double) refout . map snd $
                              forwardAD
                                (\(inelts :: [s]) ->
                                   elements' (Proxy @b)
                                     (controlfun @s
                                        (rebuildAs (Proxy @a) (Proxy @Double) input inelts)))
                                (zip (elements @a input) (elements @a tangent)))
                          x
          (refJacName, refJac) = case controlJac of
                                   Nothing -> ("forwardJac", forwardJac)
                                   Just jac -> ("controlJac", jac)
      in conjoin $
         (case controlJac of
            Nothing -> []
            Just jac ->
              [counterexample ("controlJac /= forwardJac\n" ++
                                 show jac ++ " /= " ++ show forwardJac)
                              (jac ~= forwardJac)])
         ++
         (case dofindiff of
            YesFD -> [counterexample (refJacName ++ " /= findiffJac\n" ++
                                        show refJac ++ " /= " ++ show findiffJac)
                                     (refJac ~= findiffJac)]
            NoFD -> [])
         ++
         [counterexample (refJacName ++ " /= programJac\n" ++
                            show refJac ++ " /= " ++ show programJac)
                         (refJac ~= programJac)]

data Vec3 a = Vec3 a a a deriving (Show)
data Quaternion a = Quaternion a a a a deriving (Show)

newtype Vec3N a = Vec3N (a, a, a) deriving (Show)
newtype QuaternionN a = QuaternionN (a, a, a, a) deriving (Show)

newtypeFinDiff ''Vec3N
newtypeFinDiff ''QuaternionN

instance Arbitrary a => Arbitrary (Vec3N a) where arbitrary = Vec3N <$> arbitrary
instance Arbitrary a => Arbitrary (QuaternionN a) where arbitrary = QuaternionN <$> arbitrary

instance Approx a => Approx (Vec3N a) where
  approx absdelta reldelta (Vec3N (a, b, c)) (Vec3N (a', b', c')) = approx absdelta reldelta [a, b, c] [a', b', c']

instance Approx a => Approx (QuaternionN a) where
  approx absdelta reldelta (QuaternionN (a, b, c, d)) (QuaternionN (a', b', c', d')) = approx absdelta reldelta [a, b, c, d] [a', b', c', d']

main :: IO ()
main =
  runTestsExit $
  withShowDuration True $
  changeArgs (\a -> a { maxSuccess = 50000 }) $
  tree "AD"
    [checkFDcontrol "id"
       $$(reverseADandControl @Double @Double (parseType "Double") (parseType "Double")
            [|| \x -> x ||])
       (Just (\_ d -> d))
       YesFD
    ,checkFDcontrol "plus"
       $$(reverseADandControl @(Double, Double) @Double (parseType "(Double, Double)") (parseType "Double")
            [|| \(x, y) -> x + y ||])
       (Just (\_ d -> (d,d)))
       YesFD
    ,checkFDcontrol "times"
       $$(reverseADandControl @(Double, Double) @Double (parseType "(Double, Double)") (parseType "Double")
            [|| \(x, y) -> x * y ||])
       (Just (\(x,y) d -> (y*d,x*d)))
       YesFD
    ,checkFDcontrol "let"
       $$(reverseADandControl @Double @Double (parseType "Double") (parseType "Double")
            [|| \x -> let y = 3.0 + x in x * y ||])
       (Just (\x d -> d * (2*x + 3)))
       YesFD
    ,checkFDcontrol "higher-order"
       $$(reverseADandControl @(Double, Double) @Double (parseType "(Double, Double)") (parseType "Double")
            [|| \(x,y) -> let f = \z -> x * z + y
                          in f y * f x ||])
       (Just (\(x,y) d -> (d * (3*x^2*y + 2*x*y + y^2), d * (x^3 + x^2 + 2*x*y + 2*y))))
       YesFD
    ,checkFDcontrol "higher-order2"
       $$(reverseADandControl @(Double, Double) @Double (parseType "(Double, Double)") (parseType "Double")
            [|| \(x,y) -> let f z = x * z + y
                              g f' u = f' u * f x
                              h = g f
                          in h y ||])
       (Just (\(x,y) d -> (d * (3*x^2*y + 2*x*y + y^2), d * (x^3 + x^2 + 2*x*y + 2*y))))
       YesFD
    ,checkFDcontrol "complexity"
       $$(reverseADandControl @(Double, Double) @Double (parseType "(Double, Double)") (parseType "Double")
            [|| \(x,y) -> let x1 = x + y
                              x2 = x1 + x
                              x3 = x2 + x1
                              x4 = x3 + x2
                              x5 = x4 + x3
                              x6 = x5 + x4
                              x7 = x6 + x5
                              x8 = x7 + x6
                              x9 = x8 + x7
                              x10 = x9 + x8
                          in x10 * x10 ||])
       -- x10 = 89x + 55y
       -- x10^2 = 7921x^2 + 9790xy + 3025y^2
       (Just (\(x,y) d -> (d * (2*7921*x + 9790*y), d * (9790*x + 2*3025*y))))
       YesFD
    ,checkFDcontrol "complexity2"
       $$(reverseADandControl @Double @Double (parseType "Double") (parseType "Double")
            [|| \x0 -> let x1  = x0 + x0 + x0 + x0 + x0 - x0 - x0 - x0
                           x2  = x1 + x1 + x1 + x1 + x1 - x1 - x1 - x1
                           x3  = x2 + x2 + x2 + x2 + x2 - x2 - x2 - x2
                           x4  = x3 + x3 + x3 + x3 + x3 - x3 - x3 - x3
                           x5  = x4 + x4 + x4 + x4 + x4 - x4 - x4 - x4
                           x6  = x5 + x5 + x5 + x5 + x5 - x5 - x5 - x5
                           x7  = x6 + x6 + x6 + x6 + x6 - x6 - x6 - x6
                           x8  = x7 + x7 + x7 + x7 + x7 - x7 - x7 - x7
                           x9  = x8 + x8 + x8 + x8 + x8 - x8 - x8 - x8
                           x10 = x9 + x9 + x9 + x9 + x9 - x9 - x9 - x9
                       in 0.000001 * x10 * x10 ||])
       -- xn = 2 * x{n-1}
       -- x10 = 2^10 * x
       -- x10*x10 = 2^20 * x^2
       -- The small constant is there so that finite differencing doesn't explode
       (Just (\x d -> 0.000001 * 2^21 * x * d))
       YesFD
    ,checkFDcontrol "conditional"
       $$(reverseADandControl @(Double, Double) @Double (parseType "(Double, Double)") (parseType "Double")
            [|| \(x,y) -> if x > y then x * y else x + y ||])
       (Just (\(x,y) d -> if x > y then (d * y, d * x) else (d, d)))
       NoFD
    ,checkFDcontrol "recursive"
       $$(reverseADandControl @Double @Double (parseType "Double") (parseType "Double")
            [|| \x0 -> let f = \x -> if x < 10.0 then g (x * 0.6) + 1.0 else g (x * 0.1) + 2.0
                           g = \x -> if x < 1.0 then x else f (x - 1.0) + 2.0
                       in f x0 ||])
       Nothing
       YesFD
    ,checkFDcontrol "list constr"
       $$(reverseADandControl @Double @[Double] (parseType "Double") (parseType "[Double]")
            [|| \x -> 2.0 * x : 3.0 * x : [x, x + 1.0] ||])
       (Just (\_ d -> sum (zipWith (*) [2,3,1,1] d)))
       YesFD
    ,checkFDcontrol "list case"
       $$(reverseADandControl @[Double] @Double (parseType "[Double]") (parseType "Double")
            [|| \l -> case l of [] -> 2.0
                                x : _ -> x + 3.0 ||])
       Nothing
       YesFD
    ,checkFDcontrol "Sum newtype"
       $$(reverseADandControl @(Sum Double) @Double (parseType "Sum Double") (parseType "Double")
            [|| \s -> case s of Sum x -> 2.0 * x ||])
       (Just (\_ d -> Sum (2 * d)))
       YesFD
    ,changeArgs (\a -> a { maxSuccess = 1000 }) $
     checkFDcontrol "WeirdType newtype"
       $$(reverseADandControl @(WeirdType Double Int, Double) @Double (parseType "(WeirdType Double Int, Double)") (parseType "Double")
            [|| \(MkWeirdType (n, l), x) ->
                  let mul [] = []
                      mul ((y,k):ps) = (y * x, k) : mul ps
                      times [] = 0
                      times ((_,k):ps) = k + times ps
                      iterate' k f y = if k == 0 then y else iterate' (k - 1) f (f y)
                      sum' [] = 0.0
                      sum' ((y,_):ps) = y + sum' ps
                      count = let k = n + times l in if k < 0 then -k else k
                  in sum' (iterate' (if count > 10 then 10 else count) mul l) ||])
       Nothing
       YesFD
    -- ,checkFDcontrol "quaternion newtype"
    --    $$(reverseADandControl @(Vec3N Double, QuaternionN Double) @(Vec3N Double) (parseType "(Vec3N Double, QuaternionN Double)") (parseType "Vec3N Double")
    --         [|| \(topv, topq) ->
    --               let q_to_vec (QuaternionN (x, y, z, _)) = Vec3N (x, y, z)
    --                   dot (Vec3N (px, py, pz)) (Vec3N (qx, qy, qz)) = px * qx + py * qy + pz * qz
    --                   vadd (Vec3N (px, py, pz)) (Vec3N (qx, qy, qz)) = Vec3N (px + qx, py + qy, pz + qz)
    --                   scale k (Vec3N (x, y, z)) = Vec3N (k * x, k * y, k * z)
    --                   cross (Vec3N (ax, ay, az)) (Vec3N (bx, by, bz)) = Vec3N (ay*bz - az*by, az*bz - ax*bz, ax*by - ay*bx)
    --                   norm x = sqrt (dot x x)
    --                   rotate_vec_by_quat v q =
    --                     let u = q_to_vec q
    --                         s = case q of QuaternionN (_, _, _, s) -> s
    --                     in scale (2.0 * dot u v) u `vadd` scale (s * s - dot u u) v `vadd` scale (2.0 * s) (cross u v)
    --               in rotate_vec_by_quat topv topq ||])
    --    Nothing
    --    YesFD
    -- ,checkFDcontrol "quaternion data"
    --    $$(reverseADandControl @(Vec3 Double, Quaternion Double) @(Vec3 Double) (parseType "(Vec3 Double, Quaternion Double)") (parseType "Vec3 Double")
    --         [|| \(topv, topq) ->
    --               let q_to_vec (Quaternion x y z _) = Vec3 x y z
    --                   dot (Vec3 px py pz) (Vec3 qx qy qz) = px * qx + py * qy + pz * qz
    --                   vadd (Vec3 px py pz) (Vec3 qx qy qz) = Vec3 (px + qx) (py + qy) (pz + qz)
    --                   scale k (Vec3 x y z) = Vec3 (k * x) (k * y) (k * z)
    --                   cross (Vec3 ax ay az) (Vec3 bx by bz) = Vec3 (ay*bz - az*by) (az*bz - ax*bz) (ax*by - ay*bx)
    --                   norm x = sqrt (dot x x)
    --                   rotate_vec_by_quat v q =
    --                     let u = q_to_vec q
    --                         Quaternion _ _ _ s = q
    --                     in scale (2.0 * dot u v) u `vadd` scale (s * s - dot u u) v `vadd` scale (2.0 * s) (cross u v)
    --               in rotate_vec_by_quat topv topq ||])
    --    Nothing
    --    YesFD
    ]
