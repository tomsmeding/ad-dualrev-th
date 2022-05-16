{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
module Kaas where

import Data.Map.Strict (Map)

import Language.Haskell.ReverseAD.TH
import Language.Haskell.ReverseAD.TH.Orphans
import Language.Haskell.TH.Syntax


kaas :: (Structure' (Either (Name, [MonoType]) ())
        ,Map Name (Map [MonoType] (Structure' (Either (Name, [MonoType]) ()))))
kaas = $(do ty <- [t| SRT1 Int |]
            sty <- summariseType ty
            mty <- stReplaceVarsF undefined sty
            (struc, mp) <- deriveStructureGroup @() mempty mty
            Language.Haskell.TH.Syntax.lift (struc, mp))
