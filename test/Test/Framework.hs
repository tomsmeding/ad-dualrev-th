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

import Test.Parallel


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
  -- TODO: evalParallel
  failed <- evalSequential $ runTestsTree (maxLeftWidth t) stdArgs 0 t
  if Set.null failed
    then putStrLn "All successful"
    else putStrLn $ "Failed: " ++ intercalate ", " (toList failed)

runTestsTree :: Int -> Args -> Int -> Tree -> Parallel (Set String)
runTestsTree leftwid args indent = \case
  SubTree name ts ->
    run (putStrLn (replicate (2 * indent) ' ' ++ name ++ ":"))
    *> (mconcat <$> traverse (runTestsTree leftwid args (indent + 1)) ts)
  Leaf name test ->
    let padding = leftwid - 2 * indent - length name
    in run (do putStr (replicate (2 * indent) ' ' ++ name ++ ": " ++
                         replicate padding ' ')
               hFlush stdout)
       *> ((\ok -> if ok then mempty else Set.singleton name) <$> runTest args test)
  ChangeArgs f t ->
    runTestsTree leftwid (f args) indent t

runTest :: Args -> Test -> Parallel Bool
runTest args = \case
  Prop prop ->
    let checkRes Success{} = True
        checkRes GaveUp{} = False
        checkRes Failure{} = False
        checkRes NoExpectedFailure{} = False
    in checkRes <$> Spawn (quickCheckWithResult args prop)
  Unit action ->
    Action (Spawn action) $ \case
      False -> putStrLn "FAILED"
      True -> putStrLn "Success"

maxLeftWidth :: Tree -> Int
maxLeftWidth (SubTree _ ts) = 2 + maximum (map maxLeftWidth ts)
maxLeftWidth (Leaf name _) = length name
maxLeftWidth (ChangeArgs _ t) = maxLeftWidth t
