module Language.Haskell.ReverseAD.TH.Source where

import Language.Haskell.TH (Name, Lit, Pat, Type)


data Exp
  = EVar Name
  | ECon Name
  | ELit Lit
  | EApp Exp Exp
  | ELam Pat Exp
  | ETup [Exp]
  | ECond Exp Exp Exp
  | ELet [DecGroup] Exp
  | ECase Exp [(Pat, Exp)]
  | EList [Exp]
  | ESig Exp Type
  deriving (Show)
infixl `EApp`

data DecGroup
  = DecVar Name (Maybe Type) Exp  -- ^ a single variable binding
  | DecMutGroup [(Name, Maybe Type, Pat, Exp)]  -- ^ a mutually-recursive group of function bindings
  deriving (Show)
