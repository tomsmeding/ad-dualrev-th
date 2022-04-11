{-# LANGUAGE TemplateHaskell #-}
module Kaas where

import Data.Monoid

import Language.Haskell.ReverseAD.TH


useTypeForReverseAD ''Sum
