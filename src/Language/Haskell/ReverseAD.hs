{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE ViewPatterns #-}
module Language.Haskell.ReverseAD where

import Data.Foldable (toList)
import Data.List (tails)
import Data.Int
import Data.Proxy
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Word
import Language.Haskell.TH


data Structure = SDiscrete | SScalar | STuple [Structure]
  deriving (Show)

-- TODO: use 'Language.Haskell.TH.reifyType' for this
class KnownStructure a where knownStructure :: Proxy a -> Structure
instance KnownStructure Int where knownStructure _ = SDiscrete
instance KnownStructure Int8 where knownStructure _ = SDiscrete
instance KnownStructure Int16 where knownStructure _ = SDiscrete
instance KnownStructure Int32 where knownStructure _ = SDiscrete
instance KnownStructure Int64 where knownStructure _ = SDiscrete
instance KnownStructure Word where knownStructure _ = SDiscrete
instance KnownStructure Word8 where knownStructure _ = SDiscrete
instance KnownStructure Word16 where knownStructure _ = SDiscrete
instance KnownStructure Word32 where knownStructure _ = SDiscrete
instance KnownStructure Word64 where knownStructure _ = SDiscrete
instance KnownStructure () where knownStructure _ = SDiscrete
instance KnownStructure Float where knownStructure _ = SScalar
instance KnownStructure Double where knownStructure _ = SScalar
instance (KnownStructure a, KnownStructure b) => KnownStructure (a, b) where
  knownStructure _ = STuple [knownStructure (Proxy @a), knownStructure (Proxy @b)]
instance (KnownStructure a, KnownStructure b, KnownStructure c) => KnownStructure (a, b, c) where
  knownStructure _ = STuple [knownStructure (Proxy @a), knownStructure (Proxy @b), knownStructure (Proxy @c)]
instance (KnownStructure a, KnownStructure b, KnownStructure c, KnownStructure d) => KnownStructure (a, b, c, d) where
  knownStructure _ = STuple [knownStructure (Proxy @a), knownStructure (Proxy @b), knownStructure (Proxy @c), knownStructure (Proxy @d)]

data Backpropagator a = Zero | Contribs Int [(a, Int)]
  deriving (Show)

-- | Use as follows:
--
--     > :t $$(reverseAD [|| \(x, y) -> x * y :: Double ||])
--     (Double, Double) -> (Double, Double -> (Double, Double))
reverseAD :: forall a b. (KnownStructure a, KnownStructure b)
          => Code Q (a -> b)
          -> Code Q (a -> (b, b -> a))
reverseAD (examineCode -> inputCode) =
  unsafeCodeCoerce $ do
    ex <- unType <$> inputCode
    transform (knownStructure (Proxy @a)) (knownStructure (Proxy @b)) ex

transform :: Structure -> Structure -> Exp -> Q Exp
transform inpStruc outStruc (LamE [pat] expr) = do
  argvar <- newName "arg"
  (idnum, inp) <- numberInput inpStruc (VarE argvar) 1
  idvar <- newName "i0"
  expr' <- ddr idvar expr
  let todo = "TODO: need to deinterleave the output and apply ResolveStaged still"
  return (LamE [VarP argvar] $
            LetE [ValD pat (NormalB inp) []
                 ,ValD (VarP idvar) (NormalB (LitE (IntegerL idnum))) []] $
              expr')
transform inpStruc outStruc (LamE [] body) =
  transform inpStruc outStruc body
transform inpStruc outStruc (LamE (pat : pats) body) =
  transform inpStruc outStruc (LamE [pat] (LamE pats body))
transform _ _ expr =
  fail $ "Top-level expression in reverseAD must be lambda, but is: " ++ show expr

data NumOp2 = Add | Sub | Mul
  deriving (Show)

data NumOp1 = Negate
  deriving (Show)

class DiffNum a where
  type DiffNumDual a = r | r -> a
  applyNum2 :: NumOp2 -> DiffNumDual a -> DiffNumDual a -> Int -> (DiffNumDual a, Int)
  applyNum1 :: NumOp1 -> DiffNumDual a -> Int -> (DiffNumDual a, Int)

instance DiffNum Int where
  type DiffNumDual Int = Int
  applyNum2 Add x y i = (x + y, i)
  applyNum2 Sub x y i = (x - y, i)
  applyNum2 Mul x y i = (x * y, i)
  applyNum1 Negate x i = (negate x, i)

binaryPrimOp :: (a -> a -> a)  -- ^ primal
             -> (a -> a -> (a, a))  -- ^ gradient given primals
             -> (a, Backpropagator a) -> (a, Backpropagator a) -> Int -> ((a, Backpropagator a), Int)
binaryPrimOp fun dfun (x, d1) (y, d2) i = case (d1, d2) of
  (Zero, Zero) -> ((fun x y, Zero), i)
  (Contribs i1 _, Zero) -> ((fun x y, Contribs i [(fst (dfun x y), i1)]), succ i)
  (Zero, Contribs i2 _) -> ((fun x y, Contribs i [(snd (dfun x y), i2)]), succ i)
  (Contribs i1 _, Contribs i2 _) -> let (g1, g2) = dfun x y
                                    in ((fun x y, Contribs i [(g1, i1), (g2, i2)]), succ i)

unaryPrimOp :: (a -> a)  -- ^ primal
            -> (a -> a)  -- ^ gradient given primal
            -> (a, Backpropagator a) -> Int -> ((a, Backpropagator a), Int)
unaryPrimOp fun dfun (x, d) i = case d of
  Zero -> ((fun x, Zero), i)
  Contribs j _ -> ((fun x, Contribs i [(dfun x, j)]), succ i)

instance DiffNum Double where
  type DiffNumDual Double = (Double, Backpropagator Double)
  applyNum2 Add = binaryPrimOp (+) (\_ _ -> (1.0, 1.0))
  applyNum2 Sub = binaryPrimOp (-) (\_ _ -> (1.0, -1.0))
  applyNum2 Mul = binaryPrimOp (*) (\x y -> (y, x))
  applyNum1 Negate = unaryPrimOp negate (\_ -> -1.0)

instance DiffNum Float where
  type DiffNumDual Float = (Float, Backpropagator Float)
  applyNum2 Add = binaryPrimOp (+) (\_ _ -> (1.0, 1.0))
  applyNum2 Sub = binaryPrimOp (-) (\_ _ -> (1.0, -1.0))
  applyNum2 Mul = binaryPrimOp (*) (\x y -> (y, x))
  applyNum1 Negate = unaryPrimOp negate (\_ -> -1.0)

ddr :: Name -> Exp -> Q Exp
ddr idName = \case
  VarE name -> return (TupE [Just (VarE name), Just (VarE idName)])

  LitE lit -> case lit of
    RationalL _ -> return (TupE [Just (TupE [Just (LitE lit), Just (ConE 'Zero)])
                                ,Just (VarE idName)])
    FloatPrimL _ -> fail "float prim?"
    DoublePrimL _ -> fail "double prim?"
    _ -> return (TupE [Just (LitE lit), Just (VarE idName)])

  AppE e1 e2 -> do
    e1' <- ddr idName e1
    idName1 <- newName "i1"
    e2' <- ddr idName1 e2
    idName2 <- newName "i2"
    funname <- newName "f"
    argname <- newName "a"
    return (LetE [ValD (TupP [VarP funname, VarP idName1]) (NormalB e1') []
                 ,ValD (TupP [VarP argname, VarP idName2]) (NormalB e2') []]
              (VarE funname `AppE` VarE argname `AppE` VarE idName2))

  InfixE (Just e1) (VarE opname) (Just e2) -> do
    e1' <- ddr idName e1
    idName1 <- newName "i1"
    e2' <- ddr idName1 e2
    idName2 <- newName "i2"
    case fromBinaryOperatorName opname of
      Just numop -> return $ foldl AppE (VarE 'applyNum2) [VarE numop, e1', e2', VarE idName2]
      Nothing -> fail ("Unsupported infix operator " ++ show opname)

  e@InfixE{} -> fail $ "Unsupported operator section: " ++ show e

  ParensE e -> ParensE <$> ddr idName e

  LamE [pat] e -> do
    idName1 <- newName "i"
    e' <- ddr idName1 e
    return (TupE [Just (LamE [pat, VarP idName1] e'), Just (VarE idName)])

  TupE mes
    | Just es <- sequence mes -> do
        (letwrap, vars, outid) <- ddrList es idName
        return (letwrap (TupE [Just (TupE (map (Just . VarE) vars))
                              ,Just (VarE outid)]))
    | otherwise -> notSupported "Tuple sections" (Just (show (TupE mes)))

  CondE e1 e2 e3 -> do
    e1' <- ddr idName e1
    boolName <- newName "bool"
    idName1 <- newName "i1"
    e2' <- ddr idName1 e2
    e3' <- ddr idName1 e3
    return (LetE [ValD (TupP [VarP boolName, VarP idName1]) (NormalB e1') []]
              (CondE (VarE boolName) e2' e3'))

  LetE decs body ->
    checkDecsNonRecursive decs >>= \case
      Just _ -> do
        (decs', idName') <- transDecs decs idName
        body' <- ddr idName' body
        return (LetE decs' body')
      Nothing -> notSupported "Recursive or non-variable let-bindings" (Just (show (LetE decs body)))

  ListE es -> do
    (letwrap, vars, outid) <- ddrList es idName
    return (letwrap (TupE [Just (ListE (map VarE vars))
                          ,Just (VarE outid)]))

  UnboundVarE n -> fail $ "Free variable in reverseAD: " ++ show n

  -- Constructs that we can express in terms of other, simpler constructs handled above
  LamE [] e -> ddr idName e  -- is this even a valid AST?
  LamE (pat : pats@(_:_)) e -> ddr idName (LamE [pat] (LamE pats e))
  LamCaseE mats -> do
    name <- newName "lcarg"
    ddr idName (LamE [VarP name] (CaseE (VarE name) mats))

  -- Unsupported constructs
  ConE name -> notSupported "Data constructors" (Just (show name))
  e@AppTypeE{} -> notSupported "Type applications" (Just (show e))
  e@UInfixE{} -> notSupported "UInfixE" (Just (show e))
  e@UnboxedTupE{} -> notSupported "Unboxed tuples" (Just (show e))
  e@UnboxedSumE{} -> notSupported "Unboxed sums" (Just (show e))
  e@MultiIfE{} -> notSupported "Multi-way ifs" (Just (show e))
  e@CaseE{} -> notSupported "Case expressions" (Just (show e))
  e@DoE{} -> notSupported "Do blocks" (Just (show e))
  e@MDoE{} -> notSupported "MDo blocks" (Just (show e))
  e@CompE{} -> notSupported "List comprehensions" (Just (show e))
  e@ArithSeqE{} -> notSupported "Arithmetic sequences" (Just (show e))
  e@SigE{} -> fail $ "Type ascriptions not supported, because I'm lazy and then I need to write code to rewrite types (" ++ show e ++ ")"
  e@RecConE{} -> notSupported "Records" (Just (show e))
  e@RecUpdE{} -> notSupported "Records" (Just (show e))
  e@StaticE{} -> notSupported "Cloud Haskell" (Just (show e))
  e@LabelE{} -> notSupported "Overloaded labels" (Just (show e))
  e@ImplicitParamVarE{} -> notSupported "Implicit parameters" (Just (show e))
  e@GetFieldE{} -> notSupported "Records" (Just (show e))
  e@ProjectionE{} -> notSupported "Records" (Just (show e))

-- | Given list of expressions and the input ID, returns a let-wrapper that
-- defines a variable for each item in the list, the names of those variables,
-- and the output ID name (in scope in the let-wrapper).
ddrList :: [Exp] -> Name -> Q (Exp -> Exp, [Name], Name)
ddrList es idName = do
  -- output varnames of the expressions
  names <- mapM (\idx -> (,) <$> newName ("x" ++ show idx) <*> newName ("i" ++ show idx))
                [1::Int ..]
  -- the let-binding pairs
  binds <- zipWithM3 (\ni_in (nx, ni_out) e -> do e' <- ddr ni_in e
                                                  return ((nx, ni_out), e'))
                     (idName : map snd names) names es
  let out_index = case names of
                    [] -> idName
                    l -> snd (last l)
  return (LetE [ValD (TupP [VarP nx, VarP ni]) (NormalB e) []
               | ((nx, ni), e) <- binds]
         ,map fst names
         ,out_index)

-- | Differentiate a declaration, given a variable containing the next ID to
-- generate. Modifies the declaration to bind the next ID to a new name, which
-- is returned.
transDec :: Dec -> Name -> Q (Dec, Name)
transDec dec idName = case dec of
  ValD (VarP name) (NormalB body) [] -> do
    idName1 <- newName "i"
    body' <- ddr idName body
    return (ValD (TupP [VarP name, VarP idName1]) (NormalB body') [], idName1)

  _ -> fail $ "Only plain variable let-bindings (without type-signatures!) are supported in reverseAD: " ++ show dec

-- | `sequence 'transDec'`
transDecs :: [Dec] -> Name -> Q ([Dec], Name)
transDecs [] n = return ([], n)
transDecs (d : ds) n = do
  (d', n') <- transDec d n
  (ds', n'') <- transDecs ds n'
  return (d' : ds', n'')

freeVars :: MonadFail m => Exp -> m (Set Name)
freeVars = \case
  VarE n -> return (Set.singleton n)
  ConE{} -> return mempty
  LitE{} -> return mempty
  AppE e1 e2 -> (<>) <$> freeVars e1 <*> freeVars e2
  AppTypeE e1 _ -> freeVars e1
  InfixE me1 e2 me3 -> combine [maybe (return mempty) freeVars me1
                               ,freeVars e2
                               ,maybe (return mempty) freeVars me3]
  e@UInfixE{} -> notSupported "UInfixE" (Just (show e))
  ParensE e -> freeVars e
  LamE pats e -> (Set.\\) <$> freeVars e <*> combine (map boundVars pats)
  LamCaseE mats -> combine [case mat of
                              Match pat (NormalB e) [] -> (Set.\\) <$> freeVars e <*> boundVars pat
                              _ -> fail $ "Unsupported pattern in LambdaCase (neither guards nor where-blocks supported): " ++ show mat
                           | mat <- mats]
  TupE es -> combine (map (maybe (return mempty) freeVars) es)
  UnboxedTupE es -> combine (map (maybe (return mempty) freeVars) es)
  e@UnboxedSumE{} -> notSupported "Unboxed sums" (Just (show e))
  CondE e1 e2 e3 -> combine (map freeVars [e1, e2, e3])
  e@MultiIfE{} -> notSupported "Multi-way ifs" (Just (show e))
  LetE decs body -> do
    checkDecsNonRecursive decs >>= \case
        Just tups -> (Set.\\) <$> freeVars body <*> pure (Set.fromList (map fst3 tups))
        Nothing -> fail $ "Recursive declarations in let unsupported: " ++ show (LetE decs body)
  e@CaseE{} -> notSupported "Case expressions" (Just (show e))
  e@DoE{} -> notSupported "Do blocks" (Just (show e))
  e@MDoE{} -> notSupported "MDo blocks" (Just (show e))
  e@CompE{} -> notSupported "List comprehensions" (Just (show e))
  e@ArithSeqE{} -> notSupported "Arithmetic sequences" (Just (show e))
  ListE es -> combine (map freeVars es)
  SigE e _ -> freeVars e
  e@RecConE{} -> notSupported "Records" (Just (show e))
  e@RecUpdE{} -> notSupported "Records" (Just (show e))
  e@StaticE{} -> notSupported "Cloud Haskell" (Just (show e))
  UnboundVarE n -> return (Set.singleton n)
  e@LabelE{} -> notSupported "Overloaded labels" (Just (show e))
  e@ImplicitParamVarE{} -> notSupported "Implicit parameters" (Just (show e))
  e@GetFieldE{} -> notSupported "Records" (Just (show e))
  e@ProjectionE{} -> notSupported "Records" (Just (show e))

-- | If these declarations occur in a let block, check that all dependencies go
-- backwards, i.e. it would be valid to replace the let block with a chain of
-- single-dec lets. If non-recursive, returns, for each variable defined: the
-- name, the free variables of its right-hand side, and its right-hand side.
checkDecsNonRecursive :: MonadFail m => [Dec] -> m (Maybe [(Name, Set Name, Exp)])
checkDecsNonRecursive decs = do
  let processDec :: MonadFail m => Dec -> m (Name, Set Name, Exp)
      processDec = \case
        ValD (VarP name) (NormalB e) [] -> (name,,e) <$> freeVars e
        dec -> fail $ "Unsupported declaration in let: " ++ show dec
  tups <- mapM processDec decs
  let nonRecursive :: [Name] -> Set Name -> Bool
      nonRecursive boundAfterThis frees = all (\name -> name `notElem` boundAfterThis) (toList frees)
  if all (\((_, frees, _), boundAfterThis) -> nonRecursive boundAfterThis frees)
         (zip tups (tail (tails (map fst3 tups))))
    then return (Just tups)
    else return Nothing

fst3 :: (a, b, c) -> a
fst3 (a, _, _) = a

boundVars :: MonadFail m => Pat -> m (Set Name)
boundVars = \case
  LitP _ -> return mempty
  VarP n -> return (Set.singleton n)
  TupP ps -> combine (map boundVars ps)
  UnboxedTupP ps -> combine (map boundVars ps)
  p@UnboxedSumP{} -> notSupported "Unboxed sums" (Just (show p))
  ConP _ _ ps -> combine (map boundVars ps)
  InfixP p1 _ p2 -> (<>) <$> boundVars p1 <*> boundVars p2
  p@UInfixP{} -> notSupported "UInfixP" (Just (show p))
  ParensP p -> boundVars p
  TildeP p -> boundVars p
  BangP p -> boundVars p
  AsP n p -> Set.insert n <$> boundVars p
  WildP -> return mempty
  p@RecP{} -> notSupported "Records" (Just (show p))
  ListP ps -> combine (map boundVars ps)
  SigP p _ -> boundVars p
  p@ViewP{} -> notSupported "View patterns" (Just (show p))

combine :: (Monad m, Monoid a) => [m a] -> m a
combine = fmap mconcat . sequence

notSupported :: MonadFail m => String -> Maybe String -> m a
notSupported descr mthing = fail $ descr ++ " not supported in reverseAD" ++ maybe "" (": " ++) mthing

fromBinaryOperatorName :: Name -> Maybe Name
fromBinaryOperatorName opname
  | opname == '(+) = Just 'Add
  | opname == '(-) = Just 'Sub
  | opname == '(*) = Just 'Mul
  | otherwise      = Nothing

numberInput :: Structure -> Exp -> Integer -> Q (Integer, Exp)
numberInput struc input nextid = case struc of
  SDiscrete -> return (nextid, input)
  SScalar -> return
    (succ nextid
    ,TupE [Just input
          ,Just (ConE 'Contribs
                 `AppE` ListE [TupE [Just (LitE (RationalL 1.0))
                                    ,Just (LitE (IntegerL nextid))]])])
  STuple strucs -> do
    names <- mapM (const (newName "x")) strucs
    (nextid', exps) <-
      mapAccumLM (\nextid' (s, name) -> numberInput s (VarE name) nextid')
                 nextid (zip strucs names)
    return (nextid'
           ,LetE [ValD (TupP (map VarP names)) (NormalB input) []]
                 (TupE (map Just exps)))

mapAccumLM :: Monad m => (s -> a -> m (s, b)) -> s -> [a] -> m (s, [b])
mapAccumLM = go id
  where
    go :: Monad m => ([b] -> [b]) -> (s -> a -> m (s, b)) -> s -> [a] -> m (s, [b])
    go post _ s0 [] = return (s0, post [])
    go post f s0 (x:xs) = do (s1, y) <- f s0 x
                             go (post . (y :)) f s1 xs

zipWithM3 :: Applicative m => (a -> b -> c -> m d) -> [a] -> [b] -> [c] -> m [d]
zipWithM3 f a b c = traverse (\(x,y,z) -> f x y z) (zip3 a b c)
