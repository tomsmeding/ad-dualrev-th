{-# LANGUAGE RankNTypes #-}
module ForwardAD (Fwd, forwardAD, forwardAD1) where

import Data.Coerce


newtype Fwd a = Fwd (a, a)
  deriving (Show)

forwardAD :: (forall a. (Floating a, Ord a) => [a] -> [a])
                -- ^ Function to differentiate
          -> [(Double, Double)]  -- ^ Arguments and argument tangents
          -> [(Double, Double)]  -- ^ Result with tangents
forwardAD f args = coerce (f (coerce args :: [Fwd Double]))

forwardAD1 :: (forall a. (Floating a, Ord a) => a -> [a])
                 -- ^ Function to differentiate
           -> (Double, Double)  -- ^ Argument and argument tangent
           -> [(Double, Double)]  -- ^ Result with tangents
forwardAD1 f arg = coerce (f (coerce arg :: Fwd Double))

binary :: (a -> a -> a) -> (a -> a -> a -> a -> a) -> Fwd a -> Fwd a -> Fwd a
binary f df (Fwd (x, dx)) (Fwd (y, dy)) = Fwd (f x y, df x dx y dy)

unary :: Num a => (a -> a) -> (a -> a) -> Fwd a -> Fwd a
unary f df (Fwd (x, dx)) = Fwd (f x, dx * df x)

instance (Ord a, Num a) => Num (Fwd a) where
  (+) = binary (+) (\_ dx _ dy -> dx + dy)
  (-) = binary (-) (\_ dx _ dy -> dx - dy)
  (*) = binary (*) (\x dx y dy -> x * dy + y * dx)
  negate = unary negate (\_ -> -1)
  abs = unary abs (\x -> if x < 0 then -1 else 1)
  signum = unary signum (\_ -> 0)
  fromInteger n = Fwd (fromInteger n, 0)

instance (Ord a, Floating a) => Floating (Fwd a) where
  pi = Fwd (pi, 0)
  exp = unary exp exp
  log = unary log recip
  sqrt = unary sqrt (\x -> recip (-2 * sqrt x))
  -- a(x) ^ b(x) = e ^ (b(x) * log(a(x)))
  -- ~>
  -- e ^ (b(x) * log(a(x))) * (b'(x) * log(a(x)) + b(x) * a'(x)/a(x))
  -- = a^b * (db * log(a) + b*da/a)
  (**) = binary (**) (\x dx y dy -> x ** y * (dy * log x + y * dx / x))
  -- logBase x y = log y / log x
  -- ~>
  -- (log x * dy/y + log y * dx/x) / ((log x) ^ 2)
  logBase = binary logBase (\x dx y dy ->
              let lx = log x
              in (lx * dy/y + log y * dx/x) / (lx * lx))
  sin = unary sin cos
  cos = unary cos (negate . sin)
  -- sin x / cos x
  -- ~> (cos^2 x - sin^2 x) / (cos^2 x)
  --  = 1 - tan^2 x
  tan = unary tan (\x -> 1 - tan x ^ (2 :: Int))
  asin = undefined
  acos = undefined
  atan = undefined
  sinh = undefined
  cosh = undefined
  tanh = undefined
  asinh = undefined
  acosh = undefined
  atanh = undefined

instance (Ord a, Fractional a) => Fractional (Fwd a) where
  -- dx * y^-1 + x * -1*y^-2 * dy
  -- = dx/y - x/y^2*dy
  (/) = binary (/) (\x dx y dy -> dx / y - x / (y * y) * dy)
  recip = unary recip (\x -> 1 / (x * x))
  fromRational r = Fwd (fromRational r, 0)

instance Eq a => Eq (Fwd a) where
  Fwd (x, _) == Fwd (y, _) = x == y

instance Ord a => Ord (Fwd a) where
  compare (Fwd (x, _)) (Fwd (y, _)) = compare x y
