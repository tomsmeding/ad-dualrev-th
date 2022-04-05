{-# LANGUAGE RankNTypes #-}
module Main where

import Language.Haskell.TH (Quote, Code)

import qualified Numeric.AD as AD
import qualified Language.Haskell.ReverseAD.TH as DR


newtype Function m a b = Function (forall s. (Floating s, Ord s) => Code m ([s] -> [s]))

-- radWithTH :: Function a b -> a -> (b, b -> a)
-- radWithTH

main :: IO ()
main = return ()
