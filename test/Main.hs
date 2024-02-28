{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Main where

import Prelude hiding ((^))
import qualified Prelude

import Data.Monoid (Sum(..))
import Data.Proxy
import Data.Type.Equality

import Language.Haskell.ReverseAD.TH ((|*|))

import ControlFun
import FinDiff
import ForwardAD
import Test.Approx
import Test.Framework hiding (elements, scale)
import Types


-- redefine this with a restricted type
(^) :: Num a => a -> Int -> a
(^) = (Prelude.^)


checkControl :: (Arbitrary a, Arbitrary b, Approx a, Approx b, Show a, Show b)
             => String -> (a -> (b, b -> a)) -> (a -> b) -> (a -> b -> a) -> Tree
checkControl name program controlfun controlgrad =
  property name $ \x adj ->
    let (y1, df1) = program x
    in y1 ~= controlfun x .&&. df1 adj ~= controlgrad x adj

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
checkFDcontrol name = checkFDcontrol' name (\_ -> True)

checkFDcontrol' :: forall a b.
                   (Arbitrary a, Arbitrary b, Approx a, Approx b, Show a, Show b
                   ,FinDiff a, FinDiff b, Element a ~ Double, Element b ~ Double)
                => String
                -> (a -> Bool)
                -> (a -> (b, b -> a), ControlFun a b)
                -> Maybe (a -> b -> a)
                -> DoCheckFinDiff
                -> Tree
checkFDcontrol' name precondition (program, ControlFun controlfun) mcontrolgrad dofindiff
  | Refl <- replaceElementsId @a
  , Refl <- replaceElementsId @b
  = property name $ \x -> precondition x ==>
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
          compareJacs name1 jac1 name2 jac2 =
            counterexample (name1 ++ " /= " ++ name2 ++ "\n" ++
                              show jac1 ++ " /= " ++ show jac2)
                           (jac1 ~= jac2)
      in case (controlJac, dofindiff) of
           (Just jac, _) ->
             conjoin $
               (case dofindiff of
                  YesFD -> [compareJacs "controlJac" jac "findiffJac" findiffJac]
                  NoFD -> [])
               ++
               [compareJacs "controlJac" jac "forwardJac" forwardJac
               ,compareJacs "controlJac" jac "programJac" programJac]
           (Nothing, YesFD) ->
             conjoin $
               [compareJacs "findiffJac" findiffJac "forwardJac" forwardJac
               ,compareJacs "findiffJac" findiffJac "programJac" programJac]
           (Nothing, NoFD) ->
             compareJacs "forwardJac" forwardJac "programJac" programJac

main :: IO ()
main =
  runTestsExit $
  withShowDuration True $
  changeArgs (\a -> a { maxSuccess = 50000 }) $
  tree "AD" $
    [checkFDcontrol "id"
       $$(reverseADandControl @Double @Double
            [|| \x -> x ||])
       (Just (\_ d -> d))
       YesFD] ++

    [checkFDcontrol "dup"
       $$(reverseADandControl @Double @(Double, Double)
            [|| \x -> (x, x) ||])
       (Just (\_ (d1, d2) -> d1 + d2))
       YesFD] ++

    [checkFDcontrol "plus"
       $$(reverseADandControl @(Double, Double) @Double
            [|| \(x, y) -> x + y ||])
       (Just (\_ d -> (d,d)))
       YesFD] ++

    [checkFDcontrol "times"
       $$(reverseADandControl @(Double, Double) @Double
            [|| \(x, y) -> x * y ||])
       (Just (\(x,y) d -> (y*d,x*d)))
       YesFD] ++

    [checkFDcontrol "sqrt"
       $$(reverseADandControl @Double @Double
            [|| \x -> sqrt (x * x + 1.0) ||])
       (Just (\x d -> let r = x*x + 1 in d * x / sqrt r))
       YesFD] ++

    [checkFDcontrol' "log"
       (\x -> x > 0.1)
       $$(reverseADandControl @Double @Double
            [|| \x -> log x ||])
       (Just (\x d -> d/x))
       YesFD] ++

    [checkFDcontrol' "more math"
       (\(x, y) -> x > 0 && y > 0)
       $$(reverseADandControl @(Double, Double) @Double
            [|| \(x, y) -> log x + exp y + exp (log (x * y)) ||])
       (Just (\(x, y) d -> (d*(1/x + y), d*(exp y + x))))
       NoFD] ++

    [checkFDcontrol "let"
       $$(reverseADandControl @Double @Double
            [|| \x -> let y = 3.0 + x in x * y ||])
       (Just (\x d -> d * (2*x + 3)))
       YesFD] ++

    [checkFDcontrol "let-order1"
       $$(reverseADandControl @Double @Double
            [|| \x ->
              let x1 = 2.0 * x
                  x2 = x1 * (x + x1)
                  x3 = x1 + x2 - 1.0
              in x * x3 - x2 ||])
       -- 6*x^3 - 4*x^2 - x
       (Just (\x d -> d * (18*x*x - 8*x - 1)))
       YesFD] ++

    [checkFDcontrol "let-order2"
       $$(reverseADandControl @Double @Double
            [|| \x ->
              let x3 = x1 + x2 - 1.0
                  x2 = x1 * (x + x1)
                  x1 = 2.0 * x
              in x * x3 - x2 ||])
       (Just (\x d -> d * (18*x*x - 8*x - 1)))
       YesFD] ++

    [checkFDcontrol "let-order3"
       $$(reverseADandControl @Double @Double
            [|| \x ->
              let x3 = x1 + x2 - 1.0
                  x2 = x1 * (x + x1)
                  x4 = x3 + x2
                  x1 = 2.0 * x
              in x * x3 - x4 ||])
       (Just (\x d -> d * (18*x*x - 20*x - 3)))
       YesFD] ++

    [checkFDcontrol "let-order4"
       $$(reverseADandControl @Double @Double
            [|| \x ->
              let g a = 2.0 * a
                  x2 = g x1 + 1.0
                  f a = a + 1.0
                  x1 = f (g x)
              in x1 + x2 ||])
       (Just (\_ d -> d * 6))
       YesFD] ++

    [checkFDcontrol "let-order5"
       $$(reverseADandControl @Double @Double
            [|| \x ->
              let g a = 2.0 * f a
                  x2 = g x1 + 1.0
                  f a = a + 1.0
                  x1 = f (g x)
              in x1 + x2 ||])
       (Just (\_ d -> d * 6))
       YesFD] ++

    [checkFDcontrol "higher-order"
       $$(reverseADandControl @(Double, Double) @Double
            [|| \(x,y) -> let f = \z -> x * z + y
                          in f y * f x ||])
       (Just (\(x,y) d -> (d * (3*x^2*y + 2*x*y + y^2), d * (x^3 + x^2 + 2*x*y + 2*y))))
       YesFD] ++

    [checkFDcontrol "higher-order2"
       $$(reverseADandControl @(Double, Double) @Double
            [|| \(x,y) -> let f z = x * z + y
                              g f' u = f' u * f x
                              h = g f
                          in h y ||])
       (Just (\(x,y) d -> (d * (3*x^2*y + 2*x*y + y^2), d * (x^3 + x^2 + 2*x*y + 2*y))))
       YesFD] ++

    [checkFDcontrol "composition"
       $$(reverseADandControl @(Double, Double) @Double
            [|| \(x,y) -> let f z = z * z
                              g z = 2.0 * (x - z) + y
                              h = g . f
                          in h y + (f . g) x ||])
       (Just (\(_,y) d -> (d * 2, d * (-2*y + 1))))
       YesFD] ++

    [checkFDcontrol "complexity"
       $$(reverseADandControl @(Double, Double) @Double
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
       YesFD] ++

    [checkFDcontrol "complexity2"
       $$(reverseADandControl @Double @Double
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
       YesFD] ++

    [checkFDcontrol "conditional"
       $$(reverseADandControl @(Double, Double) @Double
            [|| \(x,y) -> if x > y then x * y else x + y ||])
       (Just (\(x,y) d -> if x > y then (d * y, d * x) else (d, d)))
       NoFD] ++

    [checkFDcontrol "recursive"
       $$(reverseADandControl @Double @Double
            [|| \x0 -> let f = \x -> if x < 10.0 then g (x * 0.6) + 1.0 else g (x * 0.1) + 2.0
                           g = \x -> if x < 1.0 then x else f (x - 1.0) + 2.0
                       in f x0 ||])
       Nothing
       NoFD] ++

    [checkFDcontrol "recursive2"
       $$(reverseADandControl @Double @Double
            [|| \x0 -> let f x = if x < 10.0 then g (x * 0.6) + 1.0 else g (x * 0.1) + 2.0
                           g x = if x < 1.0 then x else f (x - 1.0) + 2.0
                       in f x0 ||])
       Nothing
       NoFD] ++

    [checkFDcontrol "list constr"
       $$(reverseADandControl @Double @[Double]
            [|| \x -> 2.0 * x : 3.0 * x : [x, x + 1.0] ||])
       (Just (\_ d -> sum (zipWith (*) [2,3,1,1] d)))
       YesFD] ++

    [checkFDcontrol "list case"
       $$(reverseADandControl @[Double] @Double
            [|| \l -> case l of [] -> 2.0
                                x : _ -> x + 3.0 ||])
       Nothing
       YesFD] ++


    [checkFDcontrol "Sum newtype"
       $$(reverseADandControl @(Sum Double) @Double
            [|| \s -> case s of Sum x -> 2.0 * x ||])
       (Just (\_ d -> Sum (2 * d)))
       YesFD] ++

    [changeArgs (\a -> a { maxSuccess = 1000 }) $
     checkFDcontrol "WeirdType newtype"
       $$(reverseADandControl @(WeirdType Double Int, Double) @Double
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
       YesFD] ++

    [checkFDcontrol "Sum newtype constr"
       $$(reverseADandControl @(Sum Double) @Double
            [|| \s -> case s of Sum x -> (case Sum 2.0 of Sum two -> two) * x ||])
       (Just (\_ d -> Sum (2 * d)))
       YesFD] ++

    [checkFDcontrol "Sum newtype constr2"
       $$(reverseADandControl @(Sum Double) @(Sum Double)
            [|| \(Sum x) -> Sum (2.0 * x) ||])
       (Just (\_ (Sum d) -> Sum (2 * d)))
       YesFD] ++

    [checkFDcontrol "Vec3 data"
       $$(reverseADandControl @(Vec3 Double) @Double
            [|| \(Vec3 x y z) -> x + y + z ||])
       (Just (\_ d -> Vec3 d d d))
       YesFD] ++

    [checkFDcontrol "Vec3 data constr"
       $$(reverseADandControl @(Vec3 Double) @(Vec3 Double)
            [|| \(Vec3 x y z) -> Vec3 (x + y) (y + z) (z + x) ||])
       (Just (\_ (Vec3 a b c) -> Vec3 (a + c) (a + b) (b + c)))
       YesFD] ++

    [checkFDcontrol "quaternion newtype"
       $$(reverseADandControl @(Vec3N Double, QuaternionN Double) @(Vec3N Double)
            [|| \(topv, topq) ->
                  let q_to_vec (QuaternionN (x, y, z, _)) = Vec3N (x, y, z)
                      dot (Vec3N (px, py, pz)) (Vec3N (qx, qy, qz)) = px * qx + py * qy + pz * qz
                      vadd (Vec3N (px, py, pz)) (Vec3N (qx, qy, qz)) = Vec3N (px + qx, py + qy, pz + qz)
                      scale k (Vec3N (x, y, z)) = Vec3N (k * x, k * y, k * z)
                      cross (Vec3N (ax, ay, az)) (Vec3N (bx, by, bz)) = Vec3N (ay*bz - az*by, az*bz - ax*bz, ax*by - ay*bx)
                      -- norm x = sqrt (dot x x)  -- present in code in paper, but unused
                      rotate_vec_by_quat v q =
                        let u = q_to_vec q
                            s = case q of QuaternionN (_, _, _, w) -> w
                        in scale (2.0 * dot u v) u `vadd` scale (s * s - dot u u) v `vadd` scale (2.0 * s) (cross u v)
                  in rotate_vec_by_quat topv topq ||])
       Nothing
       YesFD] ++

    [checkFDcontrol "quaternion data"
       $$(reverseADandControl @(Vec3 Double, Quaternion Double) @(Vec3 Double)
            [|| \(topv, topq) ->
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
       Nothing
       YesFD] ++

    [checkFDcontrol "WeirdSum data"
       $$(reverseADandControl @(WeirdSum Double Int) @Double
            [|| \v -> case v of WSOne x i y -> fromIntegral i * x * y
                                WSTwo (i, x) -> fromIntegral i + x ||])
       (Just (\inp d -> case inp of WSOne x i y -> WSOne (d * fromIntegral i * y) i (d * fromIntegral i * x)
                                    WSTwo (i, _) -> WSTwo (i, d)))
       YesFD] ++

    [checkFDcontrol "WeirdSum data constr"
       $$(reverseADandControl @Double @(WeirdSum Int Double)
            [|| \x -> if x < 0.0 then WSOne 0 1 2 else WSTwo (3.0*x, 0) ||])
       (Just (\_ d -> case d of WSOne _ _ _ -> 0.0
                                WSTwo (d', _) -> 3.0 * d'))
       YesFD] ++

    [checkFDcontrol "AltLists1"
       $$(reverseADandControl @(AltList1 Double) @Double
            [|| \l -> let sum1 (AltCons1 x l') = x + sum2 l'
                          sum1 AltNil1 = 0.0
                          sum2 (AltCons2 x l') = x + sum1 l'
                          sum2 AltNil2 = 0.0
                      in sum1 l ||])
       (Just (\l d -> d <$ l))
       YesFD] ++

    [checkFDcontrol "AltLists2"
       $$(reverseADandControl @(Int, Double) @(AltList1 Double)
            [|| \(n, value) ->
                  let unf1 i = if i == 0 then AltNil1 else AltCons1 value (unf2 (i-1))
                      unf2 i = if i == 0 then AltNil2 else AltCons2 value (unf1 (i-1))
                      min' x y = if x < y then x else y
                      max' x y = if x > y then x else y
                  in unf1 (max' 0 (min' 10 n)) ||])
       (Just (\(_, _) d -> (0, sum d)))
       YesFD] ++

    [checkFDcontrol "tuple sections"
       $$(reverseADandControl @(Double, Double, Double) @Double
            [|| \(x, y, z) ->
                  let (a,b,c) +. (d,e,f) = (a+d, b+e, c+f)
                      f1 = (y,z,)
                      f2 = (x,,y)
                      f3 = (,x,z)
                      f4 = (,z,)
                      f5 = (,,)
                      reduce (a,b,c) = a + b + c
                  in reduce $ f1 x +. f2 z +. f3 y +. f4 x y +. f5 y z x ||])
       (Just (\_ d -> (5*d, 5*d, 5*d)))
       YesFD] ++

    [checkFDcontrol "parallel small"
       $$(reverseADandControl @(Double, Double) @Double
            [|| \(x, y) ->
                  let p = (x * y * x) |*| (y + y + x)
                  in fst p + snd p ||])
       (Just (\(x, y) d -> ((2*x*y + 1) * d, (x^2 + 2) * d)))
       YesFD] ++

    [changeArgs (\a -> a { maxSuccess = 1000 }) $
     checkFDcontrol "parallel large"
       $$(reverseADandControl @(Double, Double) @Double
            [|| \(x, y) ->
                  let rotate (a, b) i =
                        if i <= 0
                          then (a, b)
                          else let ang = 0.1 + 0.05 * sin (fromIntegral i)
                               in rotate (a * cos ang - b * sin ang
                                         ,a * sin ang + b * cos ang)
                                         (i - 1)
                      n = 300 :: Int
                      out = rotate (x, y) n |*| rotate (y, x) n
                  in case out of
                       ((a1, b1), (a2, b2)) -> a1 + b1 + a2 + b2 ||])
       (Just (\_ d ->
                let ang = 300 * 0.1 + 0.05 * sum [sin (fromIntegral i) | i <- [1::Int .. 300]]
                in (d * 2 * cos ang, d * 2 * cos ang)))
       YesFD] ++

    []
