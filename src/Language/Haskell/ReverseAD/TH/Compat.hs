{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Language.Haskell.ReverseAD.TH.Compat where

import Language.Haskell.TH

#if !MIN_VERSION_template_haskell(2,19,0)
pattern LamCasesE :: [Clause] -> Exp
pattern LamCasesE cls <- (const Nothing -> Just cls)
#endif
