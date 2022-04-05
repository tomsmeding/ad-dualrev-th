{-# LANGUAGE LambdaCase #-}
module Test.Framework (
  -- * Running test trees
  runTestsExit,
  runTests,
  -- Building test trees
  tree,
  property,
  withArgs,
  changeArgs,
  withShowDuration,
  -- * Tree data types
  Tree(..), Test(..),
  -- * QuickCheck re-export
  module ExportQC,
) where

import Control.Monad ((>=>))
import Data.Foldable (toList)
import Data.List (intercalate)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified System.Clock as Clock
import System.Exit
import System.IO
import Test.QuickCheck as ExportQC hiding (property)
import qualified Test.QuickCheck as QC

import Test.Parallel


data Settings = Settings
  { setShowDuration :: Bool }
  deriving (Show)

defaultSettings :: Settings
defaultSettings = Settings False

data Test = Prop Property
          | Unit (IO Bool)

data Tree = SubTree String [Tree]
          | Leaf String Test
          | ChangeArgs (Args -> Args) Tree
          | ChangeSettings (Settings -> Settings) Tree

withArgs :: Args -> Tree -> Tree
withArgs = ChangeArgs . const

changeArgs :: (Args -> Args) -> Tree -> Tree
changeArgs = ChangeArgs

withShowDuration :: Bool -> Tree -> Tree
withShowDuration b = ChangeSettings (\s -> s { setShowDuration = b })

property :: Testable prop => String -> prop -> Tree
property name p = Leaf name (Prop (QC.property p))

tree :: String -> [Tree] -> Tree
tree = SubTree

-- | Exits with the proper exit code after tests are done
runTestsExit :: Tree -> IO ()
runTestsExit = runTests >=> (\case True -> exitSuccess
                                   False -> exitFailure)

-- | Returns whether all tests were successful
runTests :: Tree -> IO Bool
runTests t = do
  -- TODO: evalParallel
  failed <- evalSequential $ runTestsTree (maxLeftWidth t) defaultSettings stdArgs 0 t
  if Set.null failed
    then do putStrLn "All successful"
            return True
    else do putStrLn $ "Failed: " ++ intercalate ", " (toList failed)
            return False

runTestsTree :: Int -> Settings -> Args -> Int -> Tree -> Parallel (Set String)
runTestsTree leftwid settings args indent = \case
  SubTree name ts ->
    run (putStrLn (replicate (2 * indent) ' ' ++ name ++ ":"))
    *> (mconcat <$> traverse (runTestsTree leftwid settings args (indent + 1)) ts)
  Leaf name test ->
    let padding = leftwid - 2 * indent - length name
    in run (do putStr (replicate (2 * indent) ' ' ++ name ++ ": " ++
                         replicate padding ' ')
               hFlush stdout)
       *> ((\ok -> if ok then mempty else Set.singleton name) <$> runTest leftwid settings args test)
  ChangeArgs f t ->
    runTestsTree leftwid settings (f args) indent t
  ChangeSettings f t ->
    runTestsTree leftwid (f settings) args indent t

runTest :: Int -> Settings -> Args -> Test -> Parallel Bool
runTest leftwid settings args = \case
  Prop prop ->
    let checkRes Success{} = True
        checkRes GaveUp{} = False
        checkRes Failure{} = False
        checkRes NoExpectedFailure{} = False
    in checkRes . fst <$>
          Action (Spawn (timed (quickCheckWithResult args prop)))
                 (\(_, tm) -> if setShowDuration settings
                                then putStrLn (replicate (leftwid + 4) ' ' ++
                                                 "(Time taken: " ++ show tm ++ "s)")
                                else return ())
  Unit action ->
    let suffix tm | setShowDuration settings = " (Time taken: " ++ show tm ++ "s)"
                  | otherwise                = ""
    in fmap fst . Action (Spawn (timed action)) $ \case
         (False, tm) -> putStrLn $ "FAILED" ++ suffix tm
         (True, tm) -> putStrLn $ "Success" ++ suffix tm

maxLeftWidth :: Tree -> Int
maxLeftWidth (SubTree _ ts) = 2 + maximum (map maxLeftWidth ts)
maxLeftWidth (Leaf name _) = length name
maxLeftWidth (ChangeArgs _ t) = maxLeftWidth t
maxLeftWidth (ChangeSettings _ t) = maxLeftWidth t

timed :: IO a -> IO (a, Double)
timed action = do
  starttm <- Clock.getTime Clock.Monotonic
  res <- action
  endtm <- Clock.getTime Clock.Monotonic
  let diff = Clock.toNanoSecs (Clock.diffTimeSpec endtm starttm)
  return (res, fromIntegral diff / 1e9)
