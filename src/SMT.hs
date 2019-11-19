{-# LANGUAGE PatternSynonyms, ViewPatterns #-}
module SMT where

import SExpr
import qualified SimpleSMT as S
import Unbound.Generics.LocallyNameless
import qualified Data.List
import Data.Data.Lens
import Control.Lens.Plated

type Model = HashMap String SExpr

deriving instance Data S.SExpr



sOr :: [SExpr] -> SExpr
sOr i | B "true" `elem` i = B "true"
sOr i = case filter (/= B "false") i of
  [] -> B "false"
  [x] -> x
  l -> L (B "or":l) 

unAnd :: SExpr -> [SExpr]
unAnd (L (B "and":l)) = l
unAnd a = [a]

-- always matches!
-- TODO: mb version that doesn't always match?
pattern And :: [SExpr] -> SExpr
pattern And l <- (unAnd -> l) where
  And l = sAnd l
  
  

sAnd l | B "false" `elem` l = B "false"
sAnd i = case filter (/= B "true") i of
  [] -> B "true"
  [x] -> x
  l -> L (B "and":concatMap (\(And xs) -> xs) l)

sEq x y = L [B "=", x, y]

sNot (L (B "and":as)) = sOr $ fmap sNot as
sNot (L (B "or":as)) = sAnd $ fmap sNot as
sNot (B "true") = B "false"
sNot (L [B "exists",vs,b]) = L [B "forall",vs,sNot b]
sNot (L [B "forall",vs,b]) = L [B "exists",vs,sNot b]
sNot (L [B "not", x]) = x
sNot x = L [B "not", x]

sBind :: SExpr -> [(SExpr,Name SExpr)] -> SExpr -> SExpr
sBind bndr vs body = case clean_binds vs body of
  [] -> body
  l -> L [bndr, L $ fmap (\(ty,v) -> L [B (show v),ty]) l, body]
  
-- remove vars from vs that b doesn't mention
clean_binds :: [(SExpr,Name SExpr)] -> SExpr -> [(SExpr,Name SExpr)]
clean_binds vs b = filter (\(_,n) -> n `elem` mvs) vs where
  mvs :: [Name SExpr]
  mvs = toListOf fv b

-- TODO: use de bruijn? add constr to SExpr for binding forms?
sExists :: [(SExpr,Name SExpr)] -> SExpr -> SExpr
sExists = sBind (B "exists")

-- unExists :: SExpr -> Maybe ([(SExpr, Name SExpr)], SExpr)
-- unExists (L [B "exists"])

-- pattern Exists vs b M

sForall = sBind (B "forall")

sFvs :: SExpr -> [Name SExpr]
sFvs = toListOf fv


sImplies :: SExpr -> SExpr -> SExpr
sImplies x y = L [B "=>", x, y]

simplify :: SExpr -> SExpr
simplify (L (B "and":l)) = sAnd $ fmap simplify l
-- simplify (L [B "=", L [B "Tm_tree", B x, unlist -> Just l], L [B "Tm_tree", B y, unlist -> Just m]]) | x == y && length l == length m = simplify $ sAnd $ zipWith (\a b -> L [B "=", a, b]) l m
simplify x = simplify' $ rewriteOf uniplate r x where
  -- TODO: generalze to all datatypes
  -- how? mb w/ more complex SExpr type? or with table of datatypes?
  r (L [B "=", L [B "Tm_tree", B x, unlist -> Just l], L [B "Tm_tree", B y, unlist -> Just m]]) | x == y && length l == length m = Just $ sAnd $ zipWith (\a b -> L [B "=", a, b]) l m
  r (L [B "=", x, y]) | x == y = Just $ B "true"
  r (L [B "forall", _, B "true"]) = Just $ B "true"
  r _ = Nothing

  unlist (B "nil") = Just []
  unlist (L [B "insert", x, y]) = (x :) <$> unlist y
  unlist x | trace (show x) True = Nothing

simplify' = go where
  -- go (L [B "=", L [B "Tm_tree", B x, unlist -> Just l], L [B "Tm_tree", B y, unlist -> Just m]]) | x == y && length l == length m = go $ sAnd $ zipWith (\a b -> L [B "=", a, b]) l m
  go (L [B "forall", vs, b]) = L [B "forall", vs, go b]
  go (L (B "and":l)) = sAnd $ fmap go l
  go (L [B "not",x]) = sNot $ go x
  go (L (B "or":l)) = sOr $ fmap go l
  -- go (L [B "forall", vs, b]) = L [B "forall", vs, go b]
  go x = x

  -- unlist (B "nil") = Just []
  -- unlist (L [B "insert", x, y]) = (x :) <$> unlist y
  -- unlist x | trace (show x) True = Nothing

matchAnd :: (SExpr -> Maybe SExpr) -> SExpr -> Maybe SExpr
matchAnd f (And l) = if any (isJust . snd) l' then Just $ sAnd (fmap (uncurry fromMaybe) l') else Nothing
  where l' = fmap (\x -> (x, f x)) l

_And :: Traversal' SExpr SExpr
_And f (L (B "and":l)) = sAnd <$> traverse f l
_And f x = f x

_Eq :: Traversal' SExpr (SExpr, SExpr)
_Eq f (L [B "=", x, y]) = uncurry sEq <$> f (x, y)
_Eq f x = pure x

_A :: Traversal' SExpr (Name SExpr)
_A f (A x) = A <$> f x
_A _ x = pure x

pattern Eq :: SExpr -> SExpr -> SExpr
pattern Eq x y = L [B "=", x, y]

-- just uses B for everything instead of resolving binding structure
smtexpr2sexpr :: S.SExpr -> SExpr
smtexpr2sexpr (S.List l) = L (smtexpr2sexpr <$> l)
smtexpr2sexpr (S.Atom x) = B x

type Value = SExpr


is_val :: SExpr -> Bool
is_val x | traceShow x True = False

sBool :: Bool -> SExpr
sBool True = B "true"
sBool False = B "false"

-- partially evaluate by a model
modelVal :: Model -> SExpr -> SExpr
modelVal m = go where
  go :: SExpr -> SExpr
  go (Eq x y) = if is_val x && is_val y then sBool (x == y) else Eq x y
    where x' = go x
          y' = go y
    --S.Bool $ go x == go y
  go (A v) = case m ^? ix (show v) of
    Just x -> go x
    Nothing -> A v
  -- go (L l) = error $ show l
  go (L [B "let",L vs,b]) = go (rewriteOf uniplate g b) where
    g (B x) = lookup x bs
    bs = fmap (\(L [B a,b]) -> (a,b)) vs
  -- go (L [B "tm_head", x]) = S.Other $ S.Atom $ error $ show $ go x
  go x = x
  -- go x = S.Other $ S.List $ error $ show x
  -- go x = error $ show x

-- TODO: 

-- use the model to choose a branch from disjunctions
-- returns a list, where And l is an underapprox of the input
mbpOr :: Model -> SExpr -> [SExpr]
-- mbpOr _ x | traceShow x False = undefined
mbpOr _ (B "true") = []
mbpOr _ (Eq x y) = [Eq x y]
mbpOr _ (L [B "not",x]) = [x]
mbpOr m (L (B "and":l)) = mbpOr m =<< l
mbpOr m (L (B "or":l)) = case filter (not . any ((== B "false") . modelVal m)) (mbpOr m <$> l) of
  -- TODO: choose among alts with value in model & leave any without a value
  [x] -> x
  [] -> []
  l -> [sOr $ fmap sAnd l]
mbpOr _ x = [x]
-- mbpOr m x = traceShow x undefined


-- a mbp plugin:
-- * might have some state?
-- * takes a conjunction, and says which indexes to remove & which new expressions to process & a substn & new vars


pMbp m vs b = uncurry sExists $ pMbp' m vs b

-- underapprox exists vs. b
-- TODO: move some of this to sExists or mb simplify
-- TODO: add model arg
pMbp' :: Model -> [(SExpr,Name SExpr)] -> SExpr -> ([(SExpr, Name SExpr)],SExpr)
pMbp' m x y | trace (show x <> " " <> show y) False = undefined
pMbp' m vs b = case views (_And . _Eq) f b' of
  [] -> let r = simplify b' in (clean_binds vs r, r)
  ss -> pMbp' m vs $ simplify $ substs ss b'
  where
    fixEq f x = let r = f x in if r == x then x else fixEq f r

    b' = b & _And %~ fixEq g
    -- b' = (sAnd $ mbpOr m b) & _And %~ fixEq g

    ns = fmap snd vs
    f (y, A v) | elem v ns && notElem v (sFvs y) = [(v, y)]
    f (A v, y) | elem v ns && notElem v (sFvs y) = [(v, y)]
    f _ = []

    is_con (L (B "Tm_tree":_)) = True
    is_con (L (B "insert":_)) = True
    is_con _ = False

    -- notes:
    -- * theory mbps only work on conjuctions, so need to use
    -- model to choose branches of disjunctions
    -- * inequalities are dealt with by 
    -- project_nonrec in qe_datatypes.cpp & remove_unconstrained in qe_lite.cpp
    -- i think?
    -- * there's dt_solve_plugin in qe_solve_plugin.cpp
    -- seems to be just the non-model based part

    -- insert a nil => [(hd,a),(tl,nil)]
    un_con :: SExpr -> [(String, SExpr)]
    un_con (L [B "Tm_tree",nm,c]) = [("tm_head",nm),("tm_children",c)]
    un_con (L [B "insert",x,y]) = [("head",x),("tail",y)]

    -- z3 is going to hash-cons, so don't need to worry to much about duplication
    -- but we could use let if we wanted?
    g i@(Eq x y) | is_con y && (not . null) (Data.List.intersect (sFvs y) ns) = sAnd $ fmap (\(c,v) -> sEq (L [B c, x]) v) $ un_con y
    g v = v


