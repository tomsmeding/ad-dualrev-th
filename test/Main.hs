{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
module Main where

import Prelude hiding ((^))
import qualified Prelude

import FinDiff
import Language.Haskell.ReverseAD.TH
import Test.Framework


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

checkFDcontrol :: (Arbitrary a, Arbitrary b, Approx a, Approx b, Show a, Show b
                  ,FinDiff a, FinDiff b, Element a ~ Double, Element b ~ Double)
               => String -> (a -> (b, b -> a)) -> (a -> b) -> (a -> b -> a) -> Tree
checkFDcontrol name program controlfun controlgrad =
  property name $ \x ->
    let controlJac = jacobianByRows controlgrad x
        programJac = jacobianByRows (snd . program) x
        findiffJac = jacobianByFinDiff controlfun x
    in controlJac ~= programJac && controlJac ~= findiffJac

main :: IO ()
main = runTests $
  tree "AD"
    [checkFDcontrol "id"
       $$(reverseAD @Double @Double
            [|| \x -> x ||])
       (\x -> x)
       (\_ d -> d)
    ,checkFDcontrol "plus"
       $$(reverseAD @(Double, Double) @Double
            [|| \(x, y) -> x + y ||])
       (\(x,y) -> x+y)
       (\_ d -> (d,d))
    ,checkFDcontrol "times"
       $$(reverseAD @(Double, Double) @Double
            [|| \(x, y) -> x * y ||])
       (\(x,y) -> x*y)
       (\(x,y) d -> (y*d,x*d))
    ,checkFDcontrol "let"
      $$(reverseAD @Double @Double
           [|| \x -> let y = 3.0 + x in x * y ||])
      (\x -> x^2 + 3*x)
      (\x d -> d * (2*x + 3))
    ,checkFDcontrol "higher-order"
      $$(reverseAD @(Double, Double) @Double
           [|| \(x,y) -> let f = \z -> x * z + y
                         in f y * f x ||])
      (\(x,y) -> x^3*y + x^2*y + x*y^2 + y^2)
      (\(x,y) d -> (d * (3*x^2*y + 2*x*y + y^2), d * (x^3 + x^2 + 2*x*y + 2*y)))
    ,checkFDcontrol "higher-order2"
      $$(reverseAD @(Double, Double) @Double
           [|| \(x,y) -> let f = \z -> x * z + y
                             g = \f' u -> f' u * f x
                             h = g f
                         in h y ||])
      (\(x,y) -> x^3*y + x^2*y + x*y^2 + y^2)
      (\(x,y) d -> (d * (3*x^2*y + 2*x*y + y^2), d * (x^3 + x^2 + 2*x*y + 2*y)))
    ]
