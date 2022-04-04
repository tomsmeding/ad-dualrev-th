{-# LANGUAGE LambdaCase #-}
module Test.Framework (
  Tree, Test,
  runTests,
  withArgs,
) where

import System.Exit
import System.IO
import Test.QuickCheck


data Test = Prop Property
          | Unit (IO Bool)

data Tree = SubTree String [Tree]
          | Leaf String Test
          | WithArgs Args Tree

withArgs :: Args -> Tree -> Tree
withArgs = WithArgs

runTestsExit :: Tree -> IO ()
runTestsExit tree = do
  runTestsTree (maxLeftWidth tree) stdArgs 0
  exitSuccess

runTestsTree :: Int -> Args -> Int -> Tree -> IO ()
runTestsTree leftwid args indent = \case
  SubTree name ts -> do
    putStrLn (replicate (2 * indent) ' ' ++ name ++ ":")
    mapM_ (runTestsTree leftwid args (indent + 1)) ts
  Leaf name test -> do
    let padding = leftwid - 2 * indent - length name
    putStr (replicate (2 * indent) ' ' ++ name ++ replicate padding ' ' ++ ": ")
    hFlush stdout
    runTest args test
  WithArgs args' t ->
    runTestsTree leftwid args' indent t

runTest :: Args -> Test -> IO ()
runTest args = \case
  Prop prop -> quickCheckWith args prop
  Unit action -> action >>= \case
    False -> putStrLn ""

maxLeftWidth :: Tree -> Int
maxLeftWidth (SubTree _ ts) = 2 + maximum (map maxLeftWidth ts)
maxLeftWidth (Leaf name _) = length name
maxLeftWidth (WithArgs _ t) = maxLeftWidth t
