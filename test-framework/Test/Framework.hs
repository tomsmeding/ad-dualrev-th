{-# LANGUAGE LambdaCase #-}
module Test.Framework (
  -- * Running test trees
  runTestsExit,
  runTests,
  runTestsPatterns,
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
import Data.List (intercalate, tails)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified System.Clock as Clock
import System.Environment (getArgs)
import System.Exit
import System.IO
import Test.QuickCheck as ExportQC hiding (property)
import qualified Test.QuickCheck as QC

import Test.Parallel


data Settings = Settings
  { setShowDuration :: Bool
  , setPatterns :: [String] }
  deriving (Show)

defaultSettings :: Settings
defaultSettings = Settings False []

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

-- | Exits with the proper exit code after tests are done. Reads command-line arguments.
runTestsExit :: Tree -> IO ()
runTestsExit = runTests >=> (\case True -> exitSuccess
                                   False -> exitFailure)

-- | Returns whether all tests were successful. Reads command-line arguments.
runTests :: Tree -> IO Bool
runTests t = do
  settings' <- getArgs >>= parseCmdLine defaultSettings
  let settings = settings' { setPatterns = reverse (setPatterns settings') }
  runWithSettings settings t

-- | Returns whether all tests were successful. Runs only the tests whose name
-- (joined on '.') includes one of the given pattern strings.
runTestsPatterns :: [String] -> Tree -> IO Bool
runTestsPatterns pats = runWithSettings defaultSettings { setPatterns = pats }

runWithSettings :: Settings -> Tree -> IO Bool
runWithSettings settings t = do
  -- TODO: evalParallel
  failed <- evalSequential $ runTestsTree (maxLeftWidth t) settings stdArgs [] t
  if Set.null failed
    then do putStrLn "All successful"
            return True
    else do putStrLn $ "Failed: " ++ intercalate ", " (toList failed)
            return False

runTestsTree :: Int -> Settings -> Args -> [String] -> Tree -> Parallel (Set String)
runTestsTree leftwid settings args path = \case
  SubTree name ts ->
    run (putStrLn (replicate indent ' ' ++ name ++ ":"))
    *> (mconcat <$> traverse (runTestsTree leftwid settings args (name : path)) ts)
  Leaf name test
    | null (setPatterns settings) ||
          any (`isInfixOf` intercalate "." (reverse (name : path))) (setPatterns settings) ->
        let padding = leftwid - indent - length name
        in run (do putStr (replicate indent ' ' ++ name ++ ": " ++
                             replicate padding ' ')
                   hFlush stdout)
           *> ((\ok -> if ok then mempty else Set.singleton name) <$> runTest leftwid settings args test)
    | otherwise -> pure mempty
  ChangeArgs f t ->
    runTestsTree leftwid settings (f args) path t
  ChangeSettings f t ->
    runTestsTree leftwid (f settings) args path t
  where
    indent = 2 * length path

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

-- | Returned patterns are in reverse order!
parseCmdLine :: Settings -> [String] -> IO Settings
parseCmdLine s [] = return s
parseCmdLine _ ["-h"] = do
  putStrLn "Usage: test [-h] [test patterns...]\n\
           \If patterns are given, runs only tests whose path (joined on '.') contains any\n\
           \of these substrings."
  exitSuccess
parseCmdLine s (pat : args) | take 1 pat /= "-" =
  parseCmdLine s { setPatterns = pat : setPatterns s } args
parseCmdLine _ (arg : _) = do
  putStrLn $ "Unrecognised argument: " ++ arg
  exitFailure

timed :: IO a -> IO (a, Double)
timed action = do
  starttm <- Clock.getTime Clock.Monotonic
  res <- action
  endtm <- Clock.getTime Clock.Monotonic
  let diff = Clock.toNanoSecs (Clock.diffTimeSpec endtm starttm)
  return (res, fromIntegral diff / 1e9)

isInfixOf :: Eq a => [a] -> [a] -> Bool
isInfixOf small large = any (`startsWith` small) (tails large)
  where a `startsWith` b = take (length b) a == b
