{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module GenDAG where

import GHC.Generics (Generic)
import Test.QuickCheck (Arbitrary(..), sized, chooseAny, genericShrink)

import FinDiff
import Test.Approx


-- | Single-source, single-sink directed acyclic graph with binary splits.
data DAG a
  = Source
  | Extend a (DAG a)
  | Split (DAG a, DAG a) (DAG a)
  deriving (Show, Generic)

dataFinDiff ''DAG

instance Arbitrary a => Arbitrary (DAG a) where
  arbitrary = sized $ generate chooseAny arbitrary
  shrink = genericShrink

instance Approx a => Approx (DAG a) where
  approx _ _ Source Source = True
  approx absdelta reldelta (Extend x g) (Extend y g') =
    approx absdelta reldelta x y &&
      approx absdelta reldelta g g'
  approx absdelta reldelta (Split (g1, g2) g) (Split (g1', g2') g') =
    approx absdelta reldelta g1 g1' &&
    approx absdelta reldelta g2 g2' &&
    approx absdelta reldelta g g'
  approx _ _ _ _ = False

-- interpret
--   :: (a -> a -> (a, a))  -- ^ parallel execution
--   -> (a -> (a, a))  -- ^ fork
--   -> ((a, a) -> a)  -- ^ join
--   -> (a -> a)  -- ^ extend
--   -> a  -- ^ source
--   -> DAG  -- ^ the graph to interpret
--   -> a
-- interpret par fork join extend = go
--   where
--     go s Source = s
--     go s (Extend g) = extend (go s g)
--     go s (Split (g1, g2) g) =
--       let s' = go s g
--           (s1, s2) = fork s'
--           (s1', s2') = par (go s1 g1) (go s2 g2)
--       in join (s1', s2')

generate
  :: Monad m
  => m Word  -- ^ generate a random number (full domain)
  -> m a  -- ^ generate a value
  -> Int  -- ^ size parameter
  -> m (DAG a)
generate _ _ 0 = return Source
generate genword genval size =
  bernoulli 0.5 >>= \case  -- maybe extend
    True -> Extend <$> genval <*> generate genword genval size
    False -> bernoulli splitprob >>= \case  -- maybe split
      True -> do
        g1 <- generate genword genval (size `div` 3)
        g2 <- generate genword genval (size `div` 3)
        g <- generate genword genval (size `div` 3)
        return (Split (g1, g2) g)
      False -> return Source
  where
    bernoulli p = (<= limit) <$> genword
      where limit = round (fromIntegral (maxBound :: Word) * (p :: Double))
    splitprob = 1.0 - 1.0 / fromIntegral size
