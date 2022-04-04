{-# LANGUAGE LambdaCase #-}
module Test.Framework (
  -- * Running test trees
  runTests,
  -- Building test trees
  tree,
  withArgs,
  changeArgs,
  property,
  -- * Tree data types
  Tree(..), Test(..),
  -- * QuickCheck re-export
  module ExportQC,
) where

import Data.Foldable (toList)
import Data.List (intercalate)
import Data.Set (Set)
import qualified Data.Set as Set
import System.IO
import Test.QuickCheck as ExportQC hiding (property)
import qualified Test.QuickCheck as QC


data Test = Prop Property
          | Unit (IO Bool)

data Tree = SubTree String [Tree]
          | Leaf String Test
          | ChangeArgs (Args -> Args) Tree

withArgs :: Args -> Tree -> Tree
withArgs = ChangeArgs . const

changeArgs :: (Args -> Args) -> Tree -> Tree
changeArgs = ChangeArgs

property :: Testable prop => String -> prop -> Tree
property name p = Leaf name (Prop (QC.property p))

tree :: String -> [Tree] -> Tree
tree = SubTree

runTests :: Tree -> IO ()
runTests t = do
  failed <- runTestsTree (maxLeftWidth t) stdArgs 0 t
  if Set.null failed
    then putStrLn "All successful"
    else putStrLn $ "Failed: " ++ intercalate ", " (toList failed)

runTestsTree :: Int -> Args -> Int -> Tree -> IO (Set String)
runTestsTree leftwid args indent = \case
  SubTree name ts -> do
    putStrLn (replicate (2 * indent) ' ' ++ name ++ ":")
    mconcat <$> mapM (runTestsTree leftwid args (indent + 1)) ts
  Leaf name test -> do
    let padding = leftwid - 2 * indent - length name
    putStr (replicate (2 * indent) ' ' ++ name ++ ": " ++ replicate padding ' ')
    hFlush stdout
    runTest args test >>= \case
      True -> return mempty
      False -> return (Set.singleton name)
  ChangeArgs f t ->
    runTestsTree leftwid (f args) indent t

runTest :: Args -> Test -> IO Bool
runTest args = \case
  Prop prop -> do
    res <- quickCheckWithResult args prop
    return $ case res of
      Success{} -> True
      GaveUp{} -> False
      Failure{} -> False
      NoExpectedFailure{} -> False
  Unit action -> action >>= \case
    False -> putStrLn "FAILED" >> return False
    True -> putStrLn "Success" >> return True

maxLeftWidth :: Tree -> Int
maxLeftWidth (SubTree _ ts) = 2 + maximum (map maxLeftWidth ts)
maxLeftWidth (Leaf name _) = length name
maxLeftWidth (ChangeArgs _ t) = maxLeftWidth t
