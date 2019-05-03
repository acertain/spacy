{-# LANGUAGE PatternSynonyms, ViewPatterns #-}
module SMT where

import SExpr
import qualified SimpleSMT as S
import Unbound.Generics.LocallyNameless
import qualified Data.List
import Data.Data.Lens
import Control.Lens.Plated

type Model = HashMap String S.Value

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
sNot (L [B "not", x]) = x
sNot x = L [B "not", x]

sBind :: SExpr -> [(SExpr,Name SExpr)] -> SExpr -> SExpr
sBind bndr vs body = case vs' of
  [] -> body
  l -> L [bndr, L $ fmap (\(ty,v) -> L [B (show v),ty]) l, body]
  where mvs :: [Name SExpr]
        mvs = toListOf fv body
        vs' = filter (\(_,n) -> n `elem` mvs) vs
  
-- TODO: use de bruijn? add constr to SExpr for binding forms?
sExists :: [(SExpr,Name SExpr)] -> SExpr -> SExpr
sExists = sBind (B "exists")

sForall = sBind (B "forall")

sFvs :: SExpr -> [Name SExpr]
sFvs = toListOf fv




simplify :: SExpr -> SExpr
simplify (L (B "and":l)) = sAnd $ fmap simplify l
simplify x = rewriteOf uniplate r x where
  -- TODO: generalze to all datatypes
  -- how? mb w/ more complex SExpr type? or with table of datatypes?
  r (L [B "=", L [B "Tm_tree", B x, unlist -> Just l], L [B "Tm_tree", B y, unlist -> Just m]]) | x == y && length l == length m = Just $ sAnd $ zipWith (\a b -> L [B "=", a, b]) l m
  r (L [B "=", x, y]) | x == y = Just $ B "true"
  r _ = Nothing

  unlist (B "nil") = Just []
  unlist (L [B "insert", x, y]) = (x :) <$> unlist y
  unlist x | trace (show x) True = Nothing

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


-- TODO: use Maybe?
modelVal :: Model -> SExpr -> S.Value
modelVal m = go where
  go :: SExpr -> S.Value
  go (Eq x y) = S.Bool $ go x == go y
  go (A v) = case m ^? ix (show v) of
    Just x -> x
    Nothing -> error $ "Undefined var: " <> show v <> " model: " <> show m
  -- go (L l) = error $ show l
  go (L [B "tm_head", x]) = error $ show $ go x
  go x = error $ show x

-- TODO: 

-- use the model to choose a branch from disjunctions
-- returns a list, where And l is an underapprox of the input
mbpOr :: Model -> SExpr -> [SExpr]
mbpOr _ (B "true") = []
mbpOr _ (Eq x y) = [Eq x y]
mbpOr _ (L [B "not",x]) = [x]
mbpOr m (L (B "and":l)) = mbpOr m =<< l
mbpOr m (L (B "or":l)) = case filter (all ((== S.Bool True) . modelVal m)) (mbpOr m <$> l) of
  (x:_) -> x
  [] -> []
mbpOr m x = traceShow x undefined


-- a mbp plugin:
-- * might have some state?
-- * takes a conjunction, and says which indexes to remove & which new expressions to process & a substn & new vars


-- underapprox exists vs. b
-- TODO: move some of this to sExists or mb simplify
-- TODO: add model arg
pMbp :: Model -> [(SExpr,Name SExpr)] -> SExpr -> SExpr
pMbp m x y | trace (show x <> " " <> show y) False = undefined
pMbp m vs b = case views (_And . _Eq) f b' of
  [] -> sExists vs $ simplify b'
  ss -> pMbp m vs $ simplify $ substs ss b'
  where
    fixEq f x = let r = f x in if r == x then x else fixEq f r

    b' = (sAnd $ mbpOr m b) & _And %~ fixEq g

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


