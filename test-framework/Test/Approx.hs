module Test.Approx where

import Data.Functor.Identity
import Data.Monoid
import Test.QuickCheck


class Approx a where
  approx :: Double -> Double -> a -> a -> Bool

instance Approx Double where
  approx absdelta reldelta a b =
    abs (a - b) < absdelta ||
    (max (abs a) (abs b) >= 1 && abs (a - b) < reldelta * max (abs a) (abs b))

instance Approx Int where
  approx _ _ _ _ = True

instance (Approx a, Approx b) => Approx (a, b) where
  approx absdelta reldelta (a, b) (x, y) =
    approx absdelta reldelta a x &&
      approx absdelta reldelta b y

instance (Approx a, Approx b, Approx c) => Approx (a, b, c) where
  approx absdelta reldelta (a, b, c) (x, y, z) =
    approx absdelta reldelta a x &&
    approx absdelta reldelta b y &&
    approx absdelta reldelta c z

instance Approx a => Approx [a] where
  approx absdelta reldelta l1 l2 =
    foldr (&&) True (zipWith (approx absdelta reldelta) l1 l2)

instance Approx a => Approx (Sum a) where
  approx absdelta reldelta (Sum a) (Sum b) = approx absdelta reldelta a b

instance Approx a => Approx (Identity a) where
  approx absdelta reldelta (Identity a) (Identity b) = approx absdelta reldelta a b

(~=) :: (Approx a, Show a) => a -> a -> Property
a ~= b | approx 0.01 0.01 a b = property True
       | otherwise = counterexample s (property False)
  where s = "Left arg to ~= : " ++ show a ++ "\n\
            \Right arg to ~=: " ++ show b

(~~=) :: (Approx a, Show a) => a -> a -> Property
a ~~= b | approx 0.1 0.1 a b = property True
        | otherwise = counterexample s (property False)
  where s = "Left arg to ~~= : " ++ show a ++ "\n\
            \Right arg to ~~=: " ++ show b
