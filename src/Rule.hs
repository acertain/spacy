module Rule where

import Unbound.Generics.LocallyNameless
import SExpr
import SMT
import Parser
import qualified Data.List
import Data.Char (isUpper)
import Data.Data.Lens



-- TODO: rename Predicate or something
data Rule = Rule {
  _ruleName :: String,
  -- list of clauses (is an or)
  _ruleBody :: Bind [Name Term] [Clause]
}
  -- deriving (Eq, Hashable) via PtrEq Rule
  deriving (Generic, Data)


instance Eq Rule where
  Rule n _ == Rule m _ = n == m
instance Hashable Rule where
  hashWithSalt s (Rule n _) = hashWithSalt s n

instance Show Rule where
  show = _ruleName



data Term = Var (Name Term) | Constr String [Term]
  deriving (Show, Generic, Data, Eq)


newtype Clause = Clause (Bind [Name Term] (SExpr,[(Rule,[Term])]))
  deriving (Show, Generic, Data)

instance Subst Term Term where
  isvar (Var x) = Just (SubstName x)
  isvar _ = Nothing
instance Alpha Term
-- instance Subst Term Clause
instance Alpha Clause
-- instance Subst Term Rule
instance Alpha Rule

-- TODO: this is wrong since using Name Term for binding vars showing up in SExprs
-- but nor actually using unbind/Subst right now
-- instance Subst Term SExpr
 


clause :: HashMap String Rule -> [Name Term] -> String -> Clause
clause rules env src = Clause $ bind (fmap s2n fvs) $ go c
--fmap (\(Expr x xs) -> (ln x, fmap f xs)) c
  where
    c = parseClause src
    env' = fmap name2String env
    nms :: [String]
    nms = toListOf template c
    fvs = nub (filter (isUpper . head) nms) Data.List.\\ env'
    f (Expr x xs)
      | isUpper (head x) = case xs of [] -> Var $ s2n x
      | otherwise = Constr x $ fmap f xs
    ln n = case rules ^? ix n of
      Just v -> v
      Nothing -> error $ "Undefined name: " <> show n
    go (Expr x xs:ys) = case prims ^? ix x of
      Just g -> go ys & _1 %~ (\x -> sAnd [x,g $ fmap (tm2expr . f) xs])
      Nothing -> go ys & _2 %~ ((ln x, fmap f xs):)
    go [] = (B "true", [])



tm2expr :: Term -> SExpr
tm2expr (Var v) = A $ coerce v
tm2expr (Constr x xs) = tmTree x $ fmap tm2expr xs

-- tm -> int
tmInt :: SExpr -> SExpr
tmInt x = L [B "tm_int", x]

-- string -> [tm] -> tm
tmTree :: String -> [SExpr] -> SExpr
tmTree n c = L [B "Tm_tree", B ("\"" ++ n ++ "\""), list c] where
  -- construct a smt list
  list :: [SExpr] -> SExpr
  list [] = B "nil"
  list (x:xs) = L [B "insert", x, list xs]

prims :: HashMap String ([SExpr] -> SExpr)
prims = fromList [
  ("=", \[x,y] -> L [B "=", x, y]),
  ("<", \[x,y] -> L [B "<", tmInt x, tmInt y]),
  (">=", \[x,y] -> L [B ">=", tmInt x, tmInt y]),
  ("!=", \[x,y] -> L [B "not", L [B "=", x, y]])]
      
rules :: HashMap String Rule
rules = fromList $ fmap (\r -> (_ruleName r, r)) rs where
  rs = [
    rule "sort" ["X","Y"] [
      "=(X,nil),=(Y,nil)"
      ],
    prim2 "=",
    prim2 "!=",
    prim2 "<",
    prim2 ">=",
    -- rule "=" [] [],
    -- rule "<" [] [],
    -- rule ">=" [] [],
    rule "max" ["X","R"] [
      "=(X,cons(R,nil))",
      "=(X,cons(Y,Z)),max(Z,W),<(W,Y),=(R,Y)",
      "=(X,cons(Y,Z)),max(Z,W),>=(W,Y),=(R,W)"
    ]
    ]
  prim2 n = Rule { _ruleName = n , _ruleBody = bind (fmap s2n ["A","B"]) undefined }

rules' = fmap _ruleBody rules

rule name vars clauses = Rule name $ bind (fmap s2n vars) $ fmap (clause rules (fmap s2n vars)) clauses
