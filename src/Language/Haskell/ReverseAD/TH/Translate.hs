{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
module Language.Haskell.ReverseAD.TH.Translate where

import Control.Monad (zipWithM, (>=>))
import Data.Either (partitionEithers)
import Data.Foldable (toList)
import Data.Graph
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes)
import Data.Set (Set)
import qualified Data.Set as Set
import Language.Haskell.TH as TH
import Language.Haskell.ReverseAD.TH.Source as Source
import Data.Foldable (fold)


translate :: TH.Exp -> Q Source.Exp
translate = \case
  VarE name -> return $ EVar name

  ConE name -> return $ ECon name

  LitE lit -> return $ ELit lit

  -- Handle ($) specially in case the program needs the special type inference
  -- (let's hope it does not)
  VarE dollar `AppE` e1 `AppE` e2 | dollar == '($) -> EApp <$> translate e1 <*> translate e2

  AppE e1 e2 -> EApp <$> translate e1 <*> translate e2

  InfixE (Just e1) e (Just e2) ->
    translate (e `AppE` e1 `AppE` e2)

  e@InfixE{} -> fail $ "Unsupported operator section: " ++ show e

  ParensE e -> translate e

  LamE [] e -> translate e
  LamE (pat : pats) e -> ELam pat <$> translate (LamE pats e)

  TupE mes -> do
    -- compute argument and body expression for this tuple item
    let processArg i Nothing = do
          name <- newName ("x" ++ show (i :: Int))
          return (Just (VarP name), EVar name)
        processArg _ (Just e) = do
          e' <- translate e
          return (Nothing, e')

    (args, es') <- unzip <$> zipWithM processArg [1..] mes
    return $ foldr ELam (ETup es') (catMaybes args)

  CondE e1 e2 e3 -> ECond <$> translate e1 <*> translate e2 <*> translate e3

  LetE decs body -> elet <$> transDecs decs <*> translate body

  CaseE expr matches ->
    ECase <$> translate expr
          <*> traverse (\case Match pat (NormalB rhs) wdecs -> do
                                decs' <- transDecs wdecs
                                rhs' <- translate rhs
                                return (pat, elet decs' rhs')
                              Match _ GuardedB{} _ ->
                                notSupported "Guards" (Just (show (CaseE expr matches))))
                       matches

  ListE es -> EList <$> traverse translate es

  SigE e ty -> ESig <$> translate e <*> return ty

  UnboundVarE n -> fail $ "Free variable in reverseAD: " ++ show n

  LamCaseE mats -> do
    name <- newName "lcarg"
    ELam (VarP name) <$> translate (CaseE (VarE name) mats)

  -- Unsupported constructs
  e@AppTypeE{} -> notSupported "Type applications" (Just (show e))
  e@UInfixE{} -> notSupported "UInfixE" (Just (show e))
  e@UnboxedTupE{} -> notSupported "Unboxed tuples" (Just (show e))
  e@UnboxedSumE{} -> notSupported "Unboxed sums" (Just (show e))
  e@MultiIfE{} -> notSupported "Multi-way ifs" (Just (show e))
  e@DoE{} -> notSupported "Do blocks" (Just (show e))
  e@MDoE{} -> notSupported "MDo blocks" (Just (show e))
  e@CompE{} -> notSupported "List comprehensions" (Just (show e))
  e@ArithSeqE{} -> notSupported "Arithmetic sequences" (Just (show e))
  e@RecConE{} -> notSupported "Records" (Just (show e))
  e@RecUpdE{} -> notSupported "Records" (Just (show e))
  e@StaticE{} -> notSupported "Cloud Haskell" (Just (show e))
  e@LabelE{} -> notSupported "Overloaded labels" (Just (show e))
  e@ImplicitParamVarE{} -> notSupported "Implicit parameters" (Just (show e))
  e@GetFieldE{} -> notSupported "Records" (Just (show e))
  e@ProjectionE{} -> notSupported "Records" (Just (show e))
  e@LamCasesE{} -> notSupported "Lambda cases" (Just (show e))

data DesugaredDec e
  = DDVar Name e     -- x = e
  | DDSig Name Type  -- x :: e
  deriving (Show, Functor, Foldable, Traversable)

-- Convert function declarations to simple variable declarations:
--   f a b c = E
--   f d e f = F
-- becomes
--   f = \arg1 arg2 arg3 -> case (arg1, arg2, arg3) of
--                            (a, b, c) -> E
--                            (d, e, f) -> F
--
-- Furthermore, pattern bindings are converted to go via a tuple:
--   (a, Right (b, c)) = E
-- becomes
--   vartup = case E of (a, Right (b, c)) -> (a, b, c)
--   a = case vartup of (x, _, _) -> x
--   b = case vartup of (_, x, _) -> x
--   c = case vartup of (_, _, x) -> x
--
-- SigD, i.e. type signatures, are passed through unchanged.
desugarDec :: (Quote m, MonadFail m) => Dec -> m [DesugaredDec TH.Exp]
desugarDec = \case
  ValD (VarP var) (NormalB rhs) wdecs ->
    return [DDVar var (letE' wdecs rhs)]

  ValD pat (NormalB rhs) wdecs -> do
    tupname <- newName "vartup"
    xname <- newName "x"
    vars <- toList <$> boundVars pat
    let nvars = length vars
    return $
      DDVar tupname
            (CaseE (letE' wdecs rhs)
               [Match pat (NormalB (TupE (map (Just . VarE) vars))) []])
      : [DDVar var
               (CaseE (VarE tupname)
                  [Match (TupP (replicate i WildP ++ [VarP xname] ++ replicate (nvars - 1 - i) WildP))
                         (NormalB (VarE xname))
                         []])
        | (i, var) <- zip [0..] vars]

  FunD _ [] -> fail "Function declaration with empty list of clauses?"

  FunD name clauses@(_:_) ->
    case traverse fromSimpleClause clauses of
      Left err -> fail err
      Right cpairs
        | allEqual [length pats | (pats, _) <- cpairs] -> do
            let nargs = head [length pats | Clause pats _ _ <- clauses]
            argnames <- mapM (\i -> newName ("arg" ++ show i)) [1..nargs]
            let body = LamE (map VarP argnames) $
                         CaseE (TupE (map (Just . VarE) argnames))
                           [Match (TupP ps) (NormalB rhs) []
                           | (ps, rhs) <- cpairs]
            return [DDVar name body]
        | otherwise ->
            fail $ "Clauses of declaration of " ++ show name ++
                   " do not all have the same number of arguments"
    where
      fromSimpleClause (Clause pats (NormalB body) []) = Right (pats, body)
      fromSimpleClause (Clause pats (NormalB body) wdecs) =
        fromSimpleClause (Clause pats (NormalB (letE' wdecs body)) [])
      fromSimpleClause (Clause _ GuardedB{} _) =
        Left $ "Guards not supported in declaration of " ++ show name

  SigD name typ -> return [DDSig name typ]

  dec -> fail $ "Only simple declarations supported in reverseAD: " ++ show dec
  where
    allEqual :: Eq a => [a] -> Bool
    allEqual [] = True
    allEqual (x:xs) = all (== x) xs

-- | Assumes the declarations occur in a let block. Checks that the
-- non-function bindings are non-recursive.
-- Returns a wrapper that defines all of the names, the list of defined names,
-- and the set of all free variables of the collective let-block.
groupDecs :: [DesugaredDec Source.Exp] -> Q [DecGroup]
groupDecs decs = do
  let (bindings, signatures) = partitionEithers $ flip map decs $ \case
        DDVar name e -> Left (name, e)
        DDSig name ty -> Right (name, ty)

  let boundNames = Set.fromList (map fst bindings)

  let signatureMap = Map.fromList signatures

  let handleComp :: SCC (Name, Source.Exp) -> Q DecGroup
      handleComp (AcyclicSCC (name, e)) = return (DecVar name (Map.lookup name signatureMap) e)
      handleComp (CyclicSCC pairs)
        | Just res <- traverse (\case (name, ELam p e) ->
                                        Just (name, Map.lookup name signatureMap, p, e)
                                      _ -> Nothing)
                               pairs =
            return (DecMutGroup res)
        | otherwise =
            notSupported "Recursive non-function bindings" (Just (show pairs))

  tups <- concat <$> mapM (\(name, e) -> do
                              frees <- freeVars e
                              return [((name, e), name, toList (frees `Set.intersection` boundNames))])
                          bindings
  let sccs = stronglyConnComp tups  -- [(node, key, [key])] -> [SCC node]
  traverse handleComp sccs

transDecs :: [Dec] -> Q [DecGroup]
transDecs = concatMapM desugarDec >=> traverse (traverse translate) >=> groupDecs

freeVars :: Source.Exp -> Q (Set Name)
freeVars = \case
  EVar n -> return (Set.singleton n)
  ECon{} -> return mempty
  ELit{} -> return mempty
  EApp e1 e2 -> (<>) <$> freeVars e1 <*> freeVars e2
  ELam pat e -> do
    bound <- boundVars pat
    frees <- freeVars e
    return (frees Set.\\ bound)
  ETup es -> concatMapM freeVars es
  ECond e1 e2 e3 -> concatMapM freeVars [e1, e2, e3]
  ELet decgs body -> do
    (bounds, frees) <- foldMap go decgs
    bfrees <- freeVars body
    return (frees <> (bfrees Set.\\ bounds))
    where go :: DecGroup -> Q (Set Name, Set Name)
          go (DecVar n _ e) = (Set.singleton n,) <$> freeVars e
          go (DecMutGroup ds) = foldMap (\(n, _, p, e) -> goMG n p e) ds
            where
              goMG :: Name -> Pat -> Source.Exp -> Q (Set Name, Set Name)
              goMG n p e = do
                bounds <- boundVars p
                frees <- freeVars e
                return (Set.singleton n, frees Set.\\ bounds)
  ECase e ms -> (<>) <$> freeVars e <*> concatMapM go ms
    where go :: (Pat, Source.Exp) -> Q (Set Name)
          go (pat, rhs) = do
            bound <- boundVars pat
            frees <- freeVars rhs
            return (frees Set.\\ bound)
  EList es -> concatMapM (freeVars) es
  ESig e _ -> freeVars e

boundVars :: MonadFail m => Pat -> m (Set Name)
boundVars = \case
  LitP _ -> return mempty
  VarP n -> return (Set.singleton n)
  TupP ps -> concatMapM boundVars ps
  UnboxedTupP ps -> concatMapM boundVars ps
  ConP _ _ ps -> concatMapM boundVars ps
  InfixP p1 _ p2 -> (<>) <$> boundVars p1 <*> boundVars p2
  ParensP p -> boundVars p
  TildeP p -> boundVars p
  BangP p -> boundVars p
  AsP n p -> Set.insert n <$> boundVars p
  WildP -> return mempty
  ListP ps -> concatMapM boundVars ps
  SigP p _ -> boundVars p
  p@UnboxedSumP{} -> notSupported "Unboxed sums" (Just (show p))
  p@UInfixP{} -> notSupported "UInfixP" (Just (show p))
  p@RecP{} -> notSupported "Records" (Just (show p))
  p@ViewP{} -> notSupported "View patterns" (Just (show p))

notSupported :: MonadFail m => String -> Maybe String -> m a
notSupported descr mthing = fail $ descr ++ " not supported in reverseAD" ++ maybe "" (": " ++) mthing

-- | Constructs a 'LetE', but returns the rhs untouched if the list is empty
-- instead of creating an empty let block.
letE' :: [Dec] -> TH.Exp -> TH.Exp
letE' [] rhs = rhs
letE' ds rhs = LetE ds rhs

elet :: [DecGroup] -> Source.Exp -> Source.Exp
elet [] rhs = rhs
elet ds rhs = ELet ds rhs

concatMapM :: (Applicative f, Monoid m, Traversable t) => (a -> f m) -> t a -> f m
concatMapM f = fmap fold . traverse f
