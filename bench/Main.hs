{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
module Main where

import Language.Haskell.TH.Stupid
import DFunction


newtype FMult s = MkFMult (s, s)
  deriving (Show, Functor)
instance Foldable FMult where
  foldMap f (MkFMult (x, y)) = f x <> f y
instance Traversable FMult where
  sequenceA (MkFMult (x, y)) = MkFMult <$> ((,) <$> x <*> y)
fmult :: DFunction FMult
fmult = $$(makeFunction (parseType "FMult Double") [|| \arg -> case arg of MkFMult (x, y) -> x * y ||])

-- newtype FDotProd s = FDotProd ([s], [s])
-- fdotprod :: DFunction FDotProd
-- fdotprod = $$(makeFunction (GenericFunction (\x -> )))

main :: IO ()
main = return ()
