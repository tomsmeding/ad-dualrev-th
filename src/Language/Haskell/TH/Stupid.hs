{-# LANGUAGE LambdaCase #-}
{-| This module exists because of the stupid restriction that the following is not allowed:

> $$(something [t| type |])

Hence, instead use the following:

> $$(parseType "type" >>= something)
-}
module Language.Haskell.TH.Stupid (
  parseType,
) where

import Control.Applicative
import Data.Char
import Data.List (foldl', foldl1')

import Language.Haskell.TH
import Language.Haskell.TH.Stupid.Parser


parseType :: String -> Q Type
parseType s = runParser' (pType <* pspaces) s >>= \case
                Right (ty, "") -> return ty
                Right (_, _) -> fail $ "Extra unparsed input at end of " ++ show s
                Left err -> fail $ "Could not parse type from " ++ show s ++ ": " ++ err

pType :: Parser Q Type
pType = (foldl1' AppT <$> some pTypeAtom)

pTypeAtom :: Parser Q Type
pTypeAtom = pspaces >> choice
  [do label "parentheses" $ pchar '('
      ty <- pType
      choice [do l <- some (pspaces >> pchar ',' >> pType)
                 pspaces
                 pchar ')'
                 return (foldl' AppT (TupleT (length l + 1)) (ty : l))
             ,do pchar ')'
                 return ty]
  ,do label "list type" $ pchar '['
      ty <- pType
      pspaces
      pchar ']'
      return (ListT `AppT` ty)
  ,ConT <$> pCon
  ,VarT <$> pVar]

pCon :: Parser Q Name
pCon = do
  c1 <- label "constructor" $ psatisfy isUpper
  cs <- many (psatisfy (\c -> isAlphaNum c || c `elem` "_'"))
  liftParser (lookupTypeName (c1 : cs)) >>= \case
    Just name -> return name
    Nothing -> fatal $ "Type name out of scope: " ++ show (c1 : cs)

pVar :: Monad m => Parser m Name
pVar = do
  c1 <- label "variable" $ psatisfy isLower
  cs <- many (psatisfy (\c -> isAlphaNum c || c `elem` "_'"))
  return (mkName (c1 : cs))
