module Test.Approx where

import Data.Monoid


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

instance Approx a => Approx [a] where
  approx absdelta reldelta l1 l2 =
    foldr (&&) True (zipWith (approx absdelta reldelta) l1 l2)

instance Approx a => Approx (Sum a) where
  approx absdelta reldelta (Sum a) (Sum b) = approx absdelta reldelta a b

(~=) :: Approx a => a -> a -> Bool
(~=) = approx 0.01 0.01

(~~=) :: Approx a => a -> a -> Bool
(~~=) = approx 0.1 0.1

