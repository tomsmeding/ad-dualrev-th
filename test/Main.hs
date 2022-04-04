module Main where

import Control.Monad (forM_)
import Test.QuickCheck

import Language.Haskell.ReverseAD.TH


data Prop = forall a. Testable a => Prop a

instance Testable Prop where
  property (Prop p) = property p

main :: IO ()
main = do
  forM_ properties $ quickCheckWith stdArgs
  where
    properties =
      [Prop $ \x -> x == (x :: Int)]
