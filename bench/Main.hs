{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
module Main where

import DFunction


newtype FMult s = FMult (s, s)
fmult :: DFunction FMult
fmult = $$(makeFunction [|| GenericFunction (\arg -> case arg of FMult (x, y) -> x * y) ||])

-- newtype FDotProd s = FDotProd ([s], [s])
-- fdotprod :: DFunction FDotProd
-- fdotprod = $$(makeFunction (GenericFunction (\x -> )))

main :: IO ()
main = return ()
