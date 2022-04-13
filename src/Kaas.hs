{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Kaas where

import Data.Monoid

import Language.Haskell.ReverseAD.TH


newtype Iets a b = MkIets (Int, [(a, b)])

useTypeForReverseAD ''Sum
useTypeForReverseAD ''Iets
