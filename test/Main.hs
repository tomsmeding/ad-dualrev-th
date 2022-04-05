{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
module Main where

import Prelude hiding ((^))
import qualified Prelude

import Data.Proxy
import Data.Type.Equality

import ControlFun
import FinDiff
import ForwardAD
import Test.Framework hiding (elements)


(^) :: Num a => a -> Int -> a
(^) = (Prelude.^)


class Approx a where
  approx :: Double -> Double -> a -> a -> Bool

instance Approx Double where
  approx absdelta reldelta a b =
    abs (a - b) < absdelta ||
    (max (abs a) (abs b) >= 1 && abs (a - b) < reldelta * max (abs a) (abs b))

instance (Approx a, Approx b) => Approx (a, b) where
  approx absdelta reldelta (a, b) (x, y) =
    approx absdelta reldelta a x &&
      approx absdelta reldelta b y

instance Approx a => Approx [a] where
  approx absdelta reldelta l1 l2 =
    foldr (&&) True (zipWith (approx absdelta reldelta) l1 l2)

(~=) :: Approx a => a -> a -> Bool
(~=) = approx 0.01 0.01

(~~=) :: Approx a => a -> a -> Bool
(~~=) = approx 0.1 0.1

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
      let refout = controlfun x
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

main :: IO ()
main =
  runTestsExit $
  withShowDuration True $
  changeArgs (\a -> a { maxSuccess = 50000 }) $
  tree "AD"
    [checkFDcontrol "id"
       $$(reverseADandControl @Double @Double
            [|| \x -> x ||])
       (Just (\_ d -> d))
       YesFD
    ,checkFDcontrol "plus"
       $$(reverseADandControl @(Double, Double) @Double
            [|| \(x, y) -> x + y ||])
       (Just (\_ d -> (d,d)))
       YesFD
    ,checkFDcontrol "times"
       $$(reverseADandControl @(Double, Double) @Double
            [|| \(x, y) -> x * y ||])
       (Just (\(x,y) d -> (y*d,x*d)))
       YesFD
    ,checkFDcontrol "let"
       $$(reverseADandControl @Double @Double
            [|| \x -> let y = 3.0 + x in x * y ||])
       (Just (\x d -> d * (2*x + 3)))
       YesFD
    ,checkFDcontrol "higher-order"
       $$(reverseADandControl @(Double, Double) @Double
            [|| \(x,y) -> let f = \z -> x * z + y
                          in f y * f x ||])
       (Just (\(x,y) d -> (d * (3*x^2*y + 2*x*y + y^2), d * (x^3 + x^2 + 2*x*y + 2*y))))
       YesFD
    ,checkFDcontrol "higher-order2"
       $$(reverseADandControl @(Double, Double) @Double
            [|| \(x,y) -> let f = \z -> x * z + y
                              g = \f' u -> f' u * f x
                              h = g f
                          in h y ||])
       (Just (\(x,y) d -> (d * (3*x^2*y + 2*x*y + y^2), d * (x^3 + x^2 + 2*x*y + 2*y))))
       YesFD
    ,checkFDcontrol "complexity"
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
       YesFD
    ,checkFDcontrol "complexity2"
       $$(reverseADandControl @Double @Double
            [|| \x0 -> let x1  = x0 + x0 + x0 + x0 + x0 - x0 - x0 - x0 ;
                           x2  = x1 + x1 + x1 + x1 + x1 - x1 - x1 - x1 ;
                           x3  = x2 + x2 + x2 + x2 + x2 - x2 - x2 - x2 ;
                           x4  = x3 + x3 + x3 + x3 + x3 - x3 - x3 - x3 ;
                           x5  = x4 + x4 + x4 + x4 + x4 - x4 - x4 - x4 ;
                           x6  = x5 + x5 + x5 + x5 + x5 - x5 - x5 - x5 ;
                           x7  = x6 + x6 + x6 + x6 + x6 - x6 - x6 - x6 ;
                           x8  = x7 + x7 + x7 + x7 + x7 - x7 - x7 - x7 ;
                           x9  = x8 + x8 + x8 + x8 + x8 - x8 - x8 - x8 ;
                           x10 = x9 + x9 + x9 + x9 + x9 - x9 - x9 - x9
                       in 0.000001 * x10 * x10 ||])
       -- xn = 2 * x{n-1}
       -- x10 = 2^10 * x
       -- x10*x10 = 2^20 * x^2
       -- The small constant is there so that finite differencing doesn't explode
       (Just (\x d -> 0.000001 * 2^21 * x * d))
       YesFD
    ,checkFDcontrol "conditional"
       $$(reverseADandControl @(Double, Double) @Double
            [|| \(x,y) -> if x > y then x * y else x + y ||])
       (Just (\(x,y) d -> if x > y then (d * y, d * x) else (d, d)))
       NoFD
    ,checkFDcontrol "recursive"
       $$(reverseADandControl @Double @Double
            [|| \x0 -> let f = \x -> if x < 10.0 then g (x * 0.6) + 1.0 else g (x * 0.1) + 2.0
                           g = \x -> if x < 1.0 then x else f (x - 1.0) + 2.0
                       in f x0 ||])
       Nothing
       YesFD
    ,checkFDcontrol "list constr"
       $$(reverseADandControl @Double @[Double]
            [|| \x -> 2.0 * x : 3.0 * x : [x, x + 1.0] ||])
       (Just (\_ [d1, d2, d3, d4] -> 2*d1 + 3*d2 + d3 + d4))
       YesFD
    -- ,checkFDcontrol "list case"
    --    $$(reverseADandControl @[Double] @Double
    --         [|| \l -> case l of [] -> 2.0
    --                             x : xs -> x + 3.0 ||])
    --    Nothing
    --    YesFD
    ]
