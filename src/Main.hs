{-# LANGUAGE DerivingVia, ScopedTypeVariables, UndecidableInstances, ViewPatterns, TemplateHaskell, GeneralizedNewtypeDeriving, NoMonoLocalBinds, PatternSynonyms #-}
module Main where

import Unbound.Generics.LocallyNameless
import qualified Unbound.Generics.LocallyNameless.Bind
import qualified Data.IntMap.Internal
import qualified Data.IntMap.Lazy as IM
import Parser
import Data.Data.Lens
import Control.Lens.Plated
import Data.Char
import qualified Data.List
import Prelude hiding (cls, liftM)
import qualified SimpleSMT as S
import qualified Text.PrettyPrint.ANSI.Leijen as P
import Debug.Trace
import qualified Data.PQueue.Min as Q
import Control.Exception
import GHC.Stack
import SExpr
import SMT
import Control.Lens.Unsound
import System.Mem.Weak
import Data.HashSet (HashSet)
import Control.DeepSeq

-- TODO: switch away from unbound?
-- really want a version without the semi-mandatory handling of free vars + freshening (or with it easier to disable)

-- import Language.SMTLib2.Debug
-- import Language.SMTLib2.Pipe
-- import Language.SMTLib2


-- import Data.SBV
-- import qualified Data.SBV.List as L

-- SVar to just to make conversion to smt easier
-- currently, we're abu; Var instead of having a SVar
data Term = Var (Name Term) | Constr String [Term] | SExpr (Ignore SExpr)
  -- | SVar (Ignore (Name SExpr))
  deriving (Show, Generic, Data, Eq)
-- TODO: add a Body type, or mb use Term for it
-- to abstract over the [(Rule,[Term])] & be able to do non-dnf defns
newtype Clause = Clause (Bind [Name Term] [(Rule,[Term])])
  deriving (Show, Generic, Data)

-- unbind, but without freshening (just uses names as they were bound)
-- TODO: use lunbind instead?
unbindish :: (Alpha p, Alpha t) => Bind p t -> (p, t)
unbindish (Unbound.Generics.LocallyNameless.Bind.B p t) = (p, open initialCtx (nthPatFind p) t)
;
instance Subst Term Term where
  isvar (Var x) = Just (SubstName x)
  isvar _ = Nothing
instance Alpha Term
instance Subst Term Clause
instance Alpha Clause
instance Subst Term Rule
instance Alpha Rule

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

type F = Bind [Name SExpr] SExpr


deriving instance Generic a => Generic (IntMap a)
instance (Generic a, Alpha a) => Alpha (IntMap a)
instance (Generic a, Subst b a) => Subst b (IntMap a)

instance Hashable (Name a)

sexpr2smtexpr :: SExpr -> S.SExpr
sexpr2smtexpr (A n) = S.Atom $ show n
sexpr2smtexpr (B x) = S.Atom x
sexpr2smtexpr (L l) = S.List $ fmap sexpr2smtexpr l

data Query = Query {
  _queryLvl :: Int,
  _queryRule :: Rule,
  -- _queryP :: Bind [Name SExpr] SExpr
  -- TODO: remove args
  -- (only old spacer & bmc use it)
  _queryArgs :: [Term],
  -- TODO: this is bad w/ mbp (need to not project vars mentioned in R)
  -- so we should just have canonical vars for the args? or store vars in queryArgs
  -- should instead use special vars for args & use equality etc?
  -- i think z3 does this?? TODO: look at z3's mk_pob / formula_o2n


  -- TOOD: need to make sure these are disjoint w/ vars from rules
  -- z3 does that by renaming them to sk!i
  -- is good idea, let's do it!
  _queryExists :: [(SExpr,Name SExpr)],
  _queryP :: SExpr,
  _queryModel :: Model
} deriving (Show)

makeLenses ''Query
makeLenses ''Rule

instance Eq Query where
  -- TODO: change this...
  (==) = (==) `on` _queryLvl
instance Ord Query where
  compare = compare `on` _queryLvl

data PredState = PredState {
  _psSolver :: S.Solver,
  _psPredArgs :: [Name SExpr],
  _psChildRules :: HashMap (Name SExpr) (Rule,[Term],[Name SExpr],IntMap Int),
  -- -- TODO: generalize to non-dnf predicates
  -- -- for each clause,
  -- -- * assumption var to enable/disable that clause
  -- -- * for each child rule,
  -- --   - args
  -- --   - asserted reach facts
  -- --   - map lvl => asserted sigma_lvl up to before index j (still need to assert `drop j sigma_lvl`)
  -- _psClauses :: [(Name SExpr, [(Rule,[Term],[Name SExpr],IntMap Int)])],
  -- -- -- (assumption var, reach fact)
  _psRho :: [(Name SExpr, SExpr)],
  -- -- map lvl => facts
  _psSigma :: IntMap [SExpr]
} deriving (Show)

instance Show S.Solver where show _ = ""

data MState = MState {
  _queue :: Q.MinQueue Query,
  -- overapprox: facts true about the i depth unfolding of the rule
  _sigma :: HashMap Rule (Bind [Name SExpr] (IntMap SExpr)),
  -- underapprox: implies rule
  -- (forall args. reach(args) => rule(args))
  _rho :: HashMap Rule F,
  _preds :: HashMap Rule PredState,
  _solver :: S.Solver
}


makeLenses ''MState
makeLenses ''PredState

newtype M a = M { runM :: StateT MState (FreshMT IO) a }
  deriving (Monad, MonadIO, MonadState MState, Fresh, Functor, Applicative, MonadFail)

instance MonadFail m => MonadFail (FreshMT m) where
  fail = lift . fail

-- TODO: mb switch to an effects lib
class (Monad m, Fresh m, MonadIO m) => MonadS m where
  -- TODO: rename this
  liftS :: M a -> m a
instance MonadS M where
  liftS = id
instance (MonadS m, MonadTrans t, Monad (t m), Fresh (t m), MonadIO (t m)) => MonadS (t m) where
  liftS = lift . liftS

-- TODO: remove this, as it's unused
class Monad m => Declare m where
  declare :: SExpr -> Name SExpr -> m ()
instance Declare M where
  declare ty n  = do
    s <- use solver
    liftIO $ S.declare s (show n) $ sexpr2smtexpr ty
    pure ()
instance {-# OVERLAPPABLE #-} (Declare m, MonadTrans t, Monad (t m)) => Declare (t m) where
  declare n ty = lift $ declare n ty

newtype DeclaredVarsT m a = DeclaredVarsT { unDeclaredVarsT :: StateT [(SExpr,Name SExpr)] m a }
  deriving (Monad, MonadIO, Fresh, Functor, Applicative, MonadFail, MonadTrans)

instance {-# OVERLAPS #-} Declare m => Declare (DeclaredVarsT m) where
  declare ty v = DeclaredVarsT $ do
    lift $ declare ty v
    id %= ((ty,v):)

runDeclaredVarsT :: DeclaredVarsT m a -> m (a, [(SExpr,Name SExpr)])
runDeclaredVarsT m = runStateT (coerce m) []


declare' :: MonadIO m => S.Solver -> SExpr -> Name SExpr -> m ()
declare' s ty n = (liftIO $ S.declare s (show n) $ sexpr2smtexpr ty) >> pure ()


assert' :: MonadIO m => S.Solver -> SExpr -> m ()
assert' s x = liftIO $ S.assert s $ sexpr2smtexpr x

clause :: HashMap String Rule -> [Name Term] -> String -> Clause
clause rules env src = Clause $ bind (fmap s2n fvs) $ fmap (\(Expr x xs) -> (ln x, fmap f xs)) c
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

assertM :: Monad m => Bool -> m ()
assertM b = assert b $ pure ()
{-# INLINE assertM #-}

tm2expr :: Term -> SExpr
tm2expr (Var v) = A $ coerce v
tm2expr (Constr x xs) = tmTree x $ fmap tm2expr xs

inst :: (HasCallStack, Subst a b, Typeable a, Alpha b, Fresh m) => Bind [Name a] b -> [a] -> m b
inst b l = do
  (vs,c) <- unbind b
  when (length l /= length vs) $
    error $ "inst: length mismatch: " <> show (length l) <> " /= " <> show (length vs)
  pure $ substs (zip vs l) c

-- cb should return a formula, used as approx for rule(*args)
-- TODO: cb should get occ location
-- think about how 2 use it usefully
-- mb parameterize over how to do or & and?
unfold :: forall m. (Fresh m, Declare m) => (Rule -> [Term] -> m SExpr) -> Rule -> [Term] -> m SExpr
unfold strat r args = case prims ^. at (_ruleName r) of
  Just f -> pure $ f $ fmap tm2expr args
  Nothing -> do
    body <- inst (_ruleBody r) args
    fmap sOr $ for body $ \(Clause cls) -> do
      -- we define internal variables using fresh names from unbound
      -- TODO: figore out how to keep info in the smt solver instead of asserting it each query
      -- (by unfolding each rule once, then keeping around the naming of vars & using an assumption var to enable it when needed mb)
      (rvs,rhs) <- unbind cls
      for_ rvs (declare (B "Tm") . coerce)
      sAnd <$> for rhs (uncurry g)
  where g :: Rule -> [Term] -> m SExpr
        g r ys = case prims ^. at (_ruleName r) of
              Just f -> pure $ f $ fmap tm2expr ys
              Nothing -> strat r ys

unfold' :: forall m. (Fresh m, Declare m) => (Rule -> [Term] -> m SExpr) -> Clause -> m ([(SExpr, Name SExpr)], SExpr)
unfold' strat (Clause cls) = do
  -- we define internal variables using fresh names from unbound
  -- TODO: figore out how to keep info in the smt solver instead of asserting it each query
  -- (by unfolding each rule once, then keeping around the naming of vars & using an assumption var to enable it when needed mb)
  (rvs,rhs) <- unbind cls
  for_ rvs (declare (B "Tm") . coerce)
  r <- sAnd <$> for rhs (uncurry g)
  pure ((B "Tm",) <$> coerce rvs, r)
  where g :: Rule -> [Term] -> m SExpr
        g r ys = case prims ^. at (_ruleName r) of
              Just f -> pure $ f $ fmap tm2expr ys
              Nothing -> strat r ys
              
unfoldVs :: forall m. (Fresh m, Declare m) => (Rule -> [Term] -> m SExpr) -> Clause -> [Name SExpr] -> m SExpr
unfoldVs strat (Clause cls) vs = do
  (rvs,rhs) <- unbind cls
  for_ rvs (declare (B "Tm") . coerce)
  let rhs' = substs (zipWith (\n v -> (n, Var $ coerce v)) rvs vs) rhs
  sAnd <$> for rhs' (uncurry g)
  where g :: Rule -> [Term] -> m SExpr
        g r ys = case prims ^. at (_ruleName r) of
              Just f -> pure $ f $ fmap tm2expr ys
              Nothing -> strat r ys  

-- TODO: consider doing clause at a time
-- , since if doing so can keep track of what clauses remain to check
-- & allow forgetting facts without totally losing progress / be a hybrid of normal prolog evaluation
-- otoh could just keep solver instances from stack around even if forgetting facts?
-- (keep the old asserted sigma_i too)

-- returns intermediate vars.
-- only needs fresh due to unbound deficiency, doesn't actually use it for naming returned vars
unfoldP :: forall m. Fresh m =>
            (Name SExpr -> SExpr -> SExpr -> m SExpr) ->
            (Name SExpr -> Rule -> [Term] -> m SExpr) ->
            Rule -> [Term] -> m ([Name SExpr], SExpr)
unfoldP sOr strat r args = flip evalStateT (0, 0) $ do
    body <- inst (_ruleBody r) args
    clss <- ifor body $ \i (Clause cls) -> do
      (rvs,rhs) <- unbind cls
      let rvs' = fmap (\n -> s2n (name2String n ++ "_" ++ show i)) rvs
      let rhs' = substs (zipWith (\v x -> (v, Var x)) rvs rvs') rhs
      x <- sAnd <$> for rhs' (uncurry g)
      pure (rvs', x)
    let vs = foldMap fst clss
    x <- foldr1 h $ fmap (pure . snd) clss
    pure (vs, x)
    where
      h x y = do
        x' <- x
        y' <- y
        i <- _2 <%= (+1)
        lift $ sOr (s2n $ "cls_" ++ show i) x' y'
      g r ys = case prims ^. at (_ruleName r) of
              Just f -> pure $ f $ fmap tm2expr ys
              Nothing -> do
                i <- _1 <%= (+1)
                lift $ strat (s2n $ "child_" ++ show i) r ys

bmc :: Rule -> M SExpr
bmc r = unroll 10 r []
  where
    unroll :: Int -> Rule -> [Term] -> M SExpr
    unroll 0 _ _ = pure $ B "false"
    unroll k r args = unfold (unroll (k-1)) r args


ppValues :: HashMap String SExpr -> Doc
ppValues = P.vsep . fmap (\(k, v) -> P.cyan (P.text k <> " = ") <> ppSExpr v) . itoList


rule_children :: Rule -> [Rule]
rule_children = nub . toListOf template

-- TODO: use StateT

declareVars :: [(SExpr,Name SExpr)] -> M ()
declareVars vs = for_ vs (uncurry declare)

scope' :: MonadIO m => S.Solver -> m a -> m a
scope' s x = do
  liftIO $ S.push s
  r <- x
  liftIO $ S.pop s
  pure r

scope :: MonadS m => m a -> m a
scope x = do
  s <- liftS $ use solver
  liftIO $ S.push s
  r <- x
  liftIO $ S.pop s
  pure r


-- shitty greedy maxsat
-- takes list of vars/expressions to try to make true
-- (on top of the current solver context)
approx_maxsat :: S.Solver -> [SExpr] -> IO r -> IO r
approx_maxsat s [] cont = cont
approx_maxsat s (x:xs) cont = do
  S.push s
  S.assert s $ sexpr2smtexpr x
  S.check s >>= \case
    S.Sat -> approx_maxsat s xs cont <* S.pop s
    S.Unsat -> S.pop s >> approx_maxsat s xs cont
    S.Unknown -> cont

data SMTResult = Sat (HashMap String SExpr) | Unsat | Unknown
  deriving (Eq, Show)

_Sat :: Traversal' SMTResult (HashMap String SExpr)
_Sat f (Sat x) = Sat <$> f x
_Sat _ x = pure x

check :: S.Solver -> [Name SExpr] -> IO SMTResult
check s vs = S.check s >>= \case
  S.Sat -> Sat . fmap (smtexpr2sexpr . S.value) . fromList <$> S.getConsts s (fmap show vs)
  S.Unsat -> pure Unsat
  S.Unknown -> pure Unknown


check' :: S.Solver -> IO SMTResult
check' s = S.check s >>= \case
  S.Sat -> Sat <$> getModel s
  S.Unsat -> pure Unsat
  S.Unknown -> pure Unknown
  
  

getModel :: S.Solver -> IO (HashMap String SExpr)
getModel s = do
  S.check s
  r <- S.command s $ sexpr2smtexpr $ L [B "get-model"]
  let L (B "model":r') = smtexpr2sexpr r
  pure $ fromList $ fmap (\(L [B "define-fun", B x, L [], _, v]) -> (x, v)) r'


ruleState :: Rule -> M PredState
ruleState r = do
  ps <- use (preds . at r)
  case ps of
    Just v -> pure v
    Nothing -> do
      ps <- init_pred r
      preds . at r .= Just ps
      pure ps

-- _ruleState :: MonadS m => (PredState -> m PredState) -> Rule -> m 


-- nonPred :: MonadS f => (PredState -> f PredState) -> (Maybe PredState -> f (Maybe PredState))
-- nonPred f Nothing = do
--   x <- liftS init_pred 

-- TODO: spacer' is wrong in lots of ways,
-- mostly due to bad variable scoping
-- / variable collisions
-- e.g. for quantifiers, need to
-- not reuse vars from context

-- mb should just do globally unique?

-- i think spacer gets away with just primed & not & slokems
-- def need to use skolems or de bruijn or something for foralls/exists
-- or manage instantiations & don't tell z3 forall or exists
-- & don't use quantified lemmas when computing queries & new lemmas
-- 

-- TODO: ask arie how z3 deals with quantifiers when building queries & lemmas
-- 

init_pred :: Rule -> M PredState
init_pred r = do
  s <- liftIO $ do
    l <- S.newLogger 1
    s <- S.newSolver "z3" ["-smt2","-in"] $ Just l
    S.declareDatatype s "Tm" [] [
      ("Tm_int", [("tm_int", S.tInt)]),
      ("Tm_tree", [("tm_head", S.Atom "String"), ("tm_children", S.List [S.Atom "List", S.Atom "Tm"])])]
    addFinalizer s (S.stop s >> pure ())
    pure s
  -- used to determine which summary facts to enable
  declare' s (B "Int") $ s2n "lvl"
  -- we just use variable names from the input for the solver,
  -- relying on prolog not having any local binders
  -- then only need to make names for assumption vars
  let (vs,_) = unbindish (_ruleBody r)
  for_ vs (declare' s (B "Tm") . coerce)
  print vs
  print r
  (e,(m,a)) <- flip runStateT mempty $ unfoldP (g s) (f s) r (fmap Var vs)
  for_ (fst e) (declare' s (B "Tm"))
  assert' s $ sAnd a
  -- as <- for clss $ \(Clause cls) -> do
  --   v <- fresh $ s2n "cls"
  --   (cvs,cb) <- unbind cls
  --   -- let (cvs,cb) = unbindish cls
  --   liftIO $ do
  --     declare' s (B "Bool") v
  --     for_ cvs (declare' s (B "Tm") . coerce)
  --   pure (v, fmap (uncurry (,,mempty,mempty)) cb)
  -- liftIO $ S.assert s $ sexpr2smtexpr $ sOr $ fmap (A . view _1) as
  print e
  assert' s $ snd e
  pure $ PredState {
    _psSolver = s,
    _psPredArgs = coerce vs,
    _psChildRules = m,
    -- _psClauses = as,
    _psRho = mempty,
    _psSigma = mempty
  }
  where
  -- f :: S.Solver -> Name SExpr -> Rule -> [Term] -> StateT _ M SExpr
  f s n r xs = do
    declare' s (B "Bool") n
    _1 . at n .= Just (r, xs, mempty, mempty)
    _2 <>= [sImplies (A n) $ sImplies (L [B "<=", B "lvl", B "0"]) $ B "false"]
    pure $ A n
  g :: S.Solver -> Name SExpr -> SExpr -> SExpr -> StateT _ M SExpr
  g s n x y = do
    declare' s (B "Bool") n
    let v = A n
    -- this is a disjunction:
    -- need a way to get which branch was used from the model,
    -- and need to propagate info about which rules to query
    -- at the leaves (child rules), the returned vars only cause obligations if they're true
    -- so can force one to be false here
    -- in fact, doing so makes it easier to generate queries: just query whichever is true
    -- huh?
    -- TODO: this is wrong if unfold takes prims as is instead of making them only needed for true
    -- TODO: consider rewriting unfold to work top-down (pushing down assumption vars)
    _2 <>= [sEq v x, sEq (sNot v) y]
    -- _2 <>= [sImplies (sAnd [x, y]) v, sImplies (sNot v) (sNot $ sOr [x,y])]
    -- pure v
    pure $ sOr [v,sNot v]


-- TODO: could do things other than solver per pred
-- e.g. one solver, keep however many instances of each pred's sigma/rho is needed
-- to run queries, use equalities to activate them



-- TODO: currently this puts rfs to use at the start of psClauses lists, maybe return them instead?
pre_query :: Int -> PredState -> M PredState
pre_query lvl ps =
  iforOf (psChildRules .> itraversed) ps $ \a ro@(r, xs, rfs, ss) -> do
    use (preds . at r) >>= \case
      Nothing -> pure ro
      Just rs -> do
        rfs' <- case rs ^? psRho . _head of
          Just (t,f) ->
            if t `elem` rfs then pure (t:delete t rfs)
            else do
              let f' = substs (zipWith (\v x -> (v, tm2expr x)) (rs ^. psPredArgs) xs) f
              assert' s $ sImplies (A a) $ sEq (A t) f'
              pure (t:rfs)
          Nothing -> pure rfs
        let sfs = snd $ IM.split (lvl-1) (rs ^. psSigma)
        -- TODO: try just doing = i & adding to >= sigma when learning new facts:
        -- might be able to prune from higher lvls (due to more general preds)
        dss <- ifor sfs $ \i f -> do
          let f' = drop (ss ^. at i . non 0) f
          let f'' = substs (zipWith (\v x -> (v, tm2expr x)) (rs ^. psPredArgs) xs) f'
          -- TODO: should this be <= or = ?
          unless (null f') $ assert' s $ sImplies (A a) $ sImplies (L [B "<=", B "lvl", B (show i)]) $ sAnd f''
          pure $ length f
        pure (ro & _3 .~ rfs' & _4 %~ (IM.unionWith max dss))
  where s = ps ^. psSolver
  -- forOf (psClauses . traverse) ps $ \(a,l) ->
  --   fmap (a,) $ for l $ \ro@(r, xs, rfs, ss) ->
  --     use (preds . at r) >>= \case
  --       Nothing -> pure ro
  --       Just rs -> do
  --         rfs' <- case rs ^? psRho . _head of
  --           Just (t,f) ->
  --             if t `elem` rfs then pure (t:delete t rfs)
  --             else do
  --               let f' = substs (zipWith (\v x -> (v, tm2expr x)) (rs ^. psPredArgs) xs) f
  --               assert' s $ sImplies (A a) $ sEq (A t) f'
  --               pure (t:rfs)
  --           Nothing -> pure rfs
  --         let sfs = snd $ IM.split (lvl-1) (rs ^. psSigma)
  --         dss <- ifor sfs $ \i f -> do
  --           let f' = drop (ss ^. at i . non 0) f
  --           -- TODO: should this be <= or = ?
  --           unless (null f') $ assert' s $ sImplies (A a) $ sImplies (L [B "<=", B "lvl", B (show i)]) $ sAnd f'
  --           -- assert' s $ L [B "=", L [B "=", B "lvl", B (show i)], sAnd f']
  --           pure $ length f
  --         pure (ro & _3 .~ rfs' & _4 %~ (IM.unionWith max dss))
  --   where s = ps ^. psSolver


-- brainstorming for better unfold abstraction:
-- can do ors as in input program,
-- then use the model to choose a branch from disjunctions to query
-- instead of doing multiple queries, would do:
-- unsat => unreachable
-- sat => query whatever branch is true in model

-- TODO: assert no skolems in x or count skolems in x
-- mb? how's this used? is it sometimes legit to use skolems in x?
-- (when insting foralls?)
-- mb want to rename in sExists away from sk?
skolemize :: [(SExpr,Name SExpr)] -> SExpr -> ([(SExpr,Name SExpr)], SExpr)
skolemize vs x = (imap (\i (ty,_) -> (ty,  ski i)) vs, substs ss x)
        where ss = imap (\i v -> (snd v, A $ ski i)) vs
              ski i = s2n ("sk!" ++ show i)

-- (%%%=) :: Optic ? ? s t a b -> (a -> m b) -> 
-- l %%%= f = _
--   -- do
--   -- x <- 

-- ruleState rule %%%= pre_query (lvl-1)


-- type GivenSolver = (?solver :: Solver)


run_query :: Query -> M (Maybe Bool)
run_query query = do
  print $ P.blue "Querying:"
  print query
  let rule = _queryRule query
      prop = _queryP query
      lvl = _queryLvl query

  ps <- pre_query (lvl-1) =<< ruleState rule
  preds . at rule .= Just ps

  let s = ps ^. psSolver
  scope' s $ do
    assert' s (sEq (B "lvl") (B $ show lvl))
    -- TODO: deal w/ queryArgs
    assert' s prop
    let rs = ps ^. psChildRules
    let as = fmap fst $ itoList rs
    -- TODO: max also rhos
    -- actually just want to max rhos mb?
    -- or like max sum_i=alts prod_j=conj [rho_ij!=1]*p(A_ij)
    -- 
    -- TODO: maxing as is maybe bad? because it prefers clauses w/ more preds? mb just do greedy opt? or reformulate this somehow?
    liftIO (approx_maxsat s (fmap A as) (check' s)) >>= \case
      Unsat -> do
        let f = sNot $ pMbp (_queryModel query) (_queryExists query) prop
        print $ P.red "Unreachable, updating sigma with:"
        print f
        -- print prop
        preds . ix rule . psSigma . at lvl . non [] %= (++ [f])
        pure $ Just False
      Sat m -> do
        -- the child rules the model depends on
        let as' = filter (true_in_model m) as
        -- TODO: mb do any instead of only checking first?
        case find (\v -> let x = rs ^?! ix v . _3 in null x || not (true_in_model m $ head x)) as' of
          Nothing -> do
            print $ P.green "Reachable with no assumptions"
            undefined
          Just k -> if lvl < 0 then
            error "At lvl < 0 but reachable with assumptions, this is an internal error"
            else do
            let x = rs ^?! ix k
            -- TODO: need to impl the q3 paper (instantiating skolems i think)
            -- (let's check all 3 branches against it!)
            print $ P.yellow "Reachable with assumptions, querying " <> P.text (show x)
            -- TODO: need to do capture avoidant naming/substn at various points here
            (xs,q) <- unfoldP (\v x y -> pure $ if true_in_model m v then x else y) (f (lvl-1) m rs) rule (_queryArgs query)
            let argvars = fmap (\i -> s2n ("var!" ++ show i)) [1..]
            let (qvs,q') = pMbp' m (fmap (B "Tm",) xs ++ _queryExists query) $ sAnd (q:zipWith sEq (fmap A argvars) (fmap tm2expr (x ^. _2)))
            rule_ps <- ruleState (x ^. _1)
            print rule_ps
            let ruleargs = rule_ps ^. psPredArgs
            let q'' = substs (zip argvars $ fmap A ruleargs) q'
            let (sks,q3) = skolemize qvs q''
              -- case q'' of
                      -- L [B "exists", vs, b] -> let (vs',b') = skolemize vs b in sExists vs' b'
                      -- x -> x
            deepseq q'' (pure ())
            -- should mbp query and (args = vars) then skolemize
            -- 
            -- let (ss, q') = skolemize (fmap (B "Tm",) xs ++ _queryExists query) (sAnd [q, prop])

            -- print (xs, q)
            -- print $ x ^. _2
            queue %= (Q.insert $ Query {
              _queryLvl = lvl - 1,
              _queryRule = x ^. _1,
              _queryArgs = fmap Var $ coerce ruleargs,
              -- _queryExists = sks,
              -- _queryP = q3,
              _queryExists = [],
              -- _queryP = sExists sks q3,
              _queryModel = m,
              _queryP = sExists qvs q''
            })
            pure Nothing
        -- case ifind _ (ps ^. psChildRules) of
        --   Just x -> _
        --   Nothing -> _
    -- if all (not . true_in_model m) as then do
    --   _
    -- else do
    --   _
    -- ls <- for (ps ^. psClauses) $ \(cv, rls) ->
    --   scope' s $ do
    --     assert' s (A cv)
    --     let as = toListOf (traverse . _3 . _head) rls
    --     m <- liftIO $ approx_maxsat s (fmap A as) (check' s)
    --     pure (m, rls)
    -- if all ((== Unsat) . view _1) ls then do
    --   print $ P.red "Unreachable, updating sigma"
    --   undefined
    -- else
    --   let
    --       ls' = ls >>= \x -> case x ^? (_1 . _Sat) of
    --               Just m -> [x & _1 .~ m]
    --               Nothing -> []
    --   in case find (\x -> allOf (_2 . traverse . _3) (\l -> has _head l && true_in_model (x ^. _1) (head l)) x) ls' of
    --     Just x -> do
    --       print $ P.green "Reachable with no assumptions"
    --       undefined
    --     Nothing -> do
    --       print $ P.yellow "Reachable with assumptions"
    --       let (model, cls) = head ls'
    --       let (child_rule, child_args, _, _) = cls ^?! traverse . filtered (\x -> null (x ^. _3) || not (true_in_model model $ head $ x ^. _3))
    --       q <- sAnd <$> for cls (f (lvl-1) model)
    --       print q
    --       undefined
    where
      true_in_model model v = anyOf (ix (show v)) (== B "true") model
      f lvl m rls a r xs = do
        let rs = rls ^?! ix a . _3 
        ps <- ruleState r
        let c = if has _head rs && true_in_model m (head rs) then
                  fromJust $ lookup (head rs) (ps ^. psRho)
                else
                  sAnd $ concat $ toList $ snd $ IM.split (lvl-1) (ps ^. psSigma)
        print c
        pure $ substs (zipWith (\n v -> (n, tm2expr v)) (ps ^. psPredArgs) xs) c
  --   --  print ls


spacer' = (Q.minView <$> use queue) >>= \case
    Just (query, queue') -> do
      r <- run_query query
      when (isJust r) (queue .= queue')
    Nothing -> pure ()

-- run 1 loop of spacer
-- notes:
-- * if spacer returns a model, it might take more than k depth unfolding to
-- get, but if it returns unsat/k-invariants, k depth unfolding is unsat
-- TODO: to do bfs need to process pobs (that haven't been expanded yet) bigger lvl first
-- TODO(lowprio): mixed strategies that spend some time closing branches (low lvl) and some
-- on promising branches (high lvl w/ most children reachable)?
-- TODO(lowprio): what if we dynamically decide which queries/pobs to bound out?
-- instead of a global bound
spacer :: M ()
spacer = (Q.minView <$> use queue) >>= \case
  Just (query, queue') -> do
    let lvl = _queryLvl query
        rule = _queryRule query
        args = _queryArgs query
    print query
    body <- inst (_ruleBody rule) args
    ls <- for body $ \cls ->
      scope $ do
        s <- use solver
        declareVars $ _queryExists query
        ((dvs,q),as) <- flip runStateT mempty $ do
          (vs,q) <- unfold' (cook (lvl-1)) cls
          print q
          liftIO $ do
            S.assert s $ sexpr2smtexpr q
            S.assert s $ sexpr2smtexpr $ _queryP query
          pure (vs,q)
        let vs = dvs ++ _queryExists query ++ fmap ((B "Tm",) . fst) (toListOf (traverse . traverse) as)
        r <- liftIO $ approx_maxsat s (fmap A $ toListOf (traverse . traverse . _1) as) $ check s $ fmap snd vs
        -- liftIO $ print $ ppValues model
        pure (r, q, as, dvs, cls)
    if all ((== Unsat) . view _1) ls then do
      -- TODO: actually do full mbp
      print $ P.red "Unreachable, updating sigma"
      sm <- use (sigma . at rule)
      (svs,smap) <- maybe ((,mempty) <$> ruleVars rule) unbind sm
      let f = sNot $ pMbp (_queryModel query) (_queryExists query) $ sAnd (_queryP query:zipWith (\v x -> sEq (A v) (tm2expr x)) svs args)
      -- let f = sForall (_queryExists query) $ sNot $ sAnd (_queryP query:zipWith (\v x -> sEq (A v) (tm2expr x)) svs (_queryArgs query))
      print $ P.white $ P.text $ show f
      let smap' = smap & at lvl . non (B "true") %~ (\p -> sAnd [f, p])
      sigma . at rule .= Just (bind svs smap')
      queue .= queue'
    else let ls' = ls >>= \x -> case x ^? (_1 . _Sat) of
                    Just m -> [x & _1 .~ m]
                    Nothing -> []
             true_in_model model v = anyOf (ix (show v)) (== B "true") model
             als = filter (\x -> allOf (_3 . traverse . traverse . _1) (true_in_model (x ^. _1)) x) ls'
      in
      if (not . null) als then do
        let (model, _, as, vs, cls) = als ^?! _head
        -- TODO: should make rho = branch that was reachable
        print $ P.green "Reachable with no assumptions"
        avs <- ruleVars rule
        -- (avs,_) <- unbind (query ^. queryRule . ruleBody)
        -- (ua,uvs) <- runDeclaredVarsT $ unfold (\x y -> liftS $ under x y) rule $ fmap Var $ coerce avs
        (ua,uvs) <- runDeclaredVarsT $ unfold (\x y -> liftS $ under x y) rule $ fmap Var $ coerce avs
        -- TODO: is this right
        -- should minimize the exists here
        print ua
        -- TODO: this is hack since z3 is unhappy about non top level exists even if no alternations
        -- revisit this once we impl skolems
        -- z3 projects here depending on a flag
        rho . at (_queryRule query) .= Just (bind avs $ sExists uvs ua)
        -- rho . at (_queryRule query) .= Just (bind avs $ pMbp (als ^?! _head . _1) uvs ua)
        queue .= queue'
      else if lvl <= 0 then
        -- TODO: should this be <= -1?
        queue .= queue'
      else do
        print $ P.yellow "Reachable with assumptions: " <> P.text (show $ fmap (^. _3) ls')
        -- TODO: should we only queue first so that later branches can use improved sigmas?
        for_ ls' $ \(model, _, as, vs, cls) -> do
          print as
          print model
          -- TODO: mb have type RuleTag = (Rule, Int) for nth occ of rule
          -- & use that to simplify this stuff (unfold variants)
          let (child_rule,(child_avar,child_args)) = as ^@?! (itraversed <. traverse . filtered (not . true_in_model model . fst))
          (q,_) <- flip runStateT (as & fmap reverse) $ unfoldVs (cook_with_model model child_avar (lvl-1)) cls $ fmap snd vs
          -- TODO: mbp here
          -- (need to not mbp out vars in queryArgs, or add vars for args & conjoin args = vars & mbp out all other vars)
          queue %= (Q.insert $ Query {
            _queryLvl = lvl - 1,
            _queryRule = child_rule,
            _queryArgs = child_args,
            _queryExists = vs ++ _queryExists query,
            _queryP = sAnd [q, _queryP query],
            -- TODO: this is wrong :/, need model of dvs'
            _queryModel = model
          })
          pure ()

  Nothing -> pure ()
  where
    -- each rule has a list of it's instances
    -- for each instance, we store args & bool var which signals if underapprox was satisfied by model (in which case don't need to query that rule)
    cook :: Int -> Rule -> [Term] -> StateT (HashMap Rule [(Name SExpr,[Term])])
     M SExpr
    cook lvl r ys = do
      a <- fresh $ s2n (r ^. ruleName)
      liftS $ declare (B "Bool") a
      o <- liftS $ over lvl r ys
      u <- liftS $ under r ys
      at r . non [] %= ((a,ys):)
      pure $ sAnd [o, L [B "=", A a, u]]

    cook_with_model :: Model -> Name SExpr -> Int -> Rule -> [Term] -> StateT (HashMap Rule [(Name SExpr,a)]) M SExpr
    cook_with_model m qr lvl r ys = do
      Just ((x,_):xs) <- use (at r)
      at r .= Just xs
      if x == qr then do
        print ys
        pure $ B "true"
      else case modelVal m (A x) of
        B "true" -> do
          -- TODO: should we just do under?
          o <- liftS $ over lvl r ys
          u <- liftS $ under r ys
          pure $ sAnd [u, o]
        B "false" -> liftS $ over lvl r ys
    --   -- case x of
    --   --   Just True -> do
    --   --     o <- liftS $ over lvl r ys
    --   --     u <- liftS $ under r ys
    --   --     pure $ sAnd [u, o]
    --   --   Just False -> liftS $ over lvl r ys
    --   --   Nothing -> do
    --   --     print ys
    --   --     _2 .= Just ys
    --   --     -- TODO: is this good? z3 doesn't do it i think
    --   --     liftS $ over lvl r ys

    under :: Rule -> [Term] -> M SExpr
    under r ys = 
      preuse (rho . ix r) >>= \case
        Nothing -> pure $ B "false"
        Just f -> inst f $ fmap tm2expr ys

    -- conjunction of all sigmas >= lvl
    over :: Int -> Rule -> [Term] -> M SExpr
    over lvl _ _ | lvl < 0 = pure $ B "false"
    over lvl r ys =
      preuse (sigma . ix r) >>= \case
        Nothing -> pure $ B "true"
        Just f -> do
          fs <- inst f $ fmap tm2expr ys
          let fs2 = snd $ IM.split (lvl-1) fs
          pure $ sAnd $ toList fs2

    ruleVars :: Rule -> M [Name SExpr]
    ruleVars r = coerce . fst <$> unbind (r ^. ruleBody)


run m = do
  l <- S.newLogger 1
  s <- S.newSolver "z3" ["-smt2","-in"] $ Just l
  let st = MState mempty mempty mempty mempty s
  S.declareDatatype s "Tm" [] [
    ("Tm_int", [("tm_int", S.tInt)]),
    ("Tm_tree", [("tm_head", S.Atom "String"), ("tm_children", S.List [S.Atom "List", S.Atom "Tm"])])]
  runFreshMT $ flip runStateT st $ runM m


g = run $ do
  s <- use solver
  -- S.declareDatatype s "List" ["X"] [("cons", [("head", S.Atom "X"), ("tail", S.List [S.Atom "List", S.Atom "X"])])]
  e <- bmc $ rule "goal" [] ["max(X,Y)"]
  -- e <- runFreshMT $ bmc s $ rule "goal" [] ["max(cons(X,nil),X)"]
  liftIO $ do
    S.assert s $ sexpr2smtexpr e
    Sat model <- check s $ fmap s2n ["X1","Y"]
    print $ ppValues model

ruleQ :: Rule -> Int -> M Query
ruleQ r lvl = do
  (vs,rl) <- unbind $ _ruleBody r
  print $ P.white $ "Querying lvl " <> P.text (show lvl)
  pure $ Query {
    _queryLvl = lvl,
    _queryRule = r,
    _queryExists = (B "Tm",) <$> coerce vs,
    _queryP = B "true",
    _queryArgs = fmap Var vs,
    _queryModel = mempty
  }


spacer_n :: (Int -> M Query) -> M ()
spacer_n f = do
  x <- f 0
  queue %= Q.insert x
  replicateM_ 20 spacer'
  q <- use queue
  when (Q.null q) $ spacer_n (\i -> f (i + 1))

e = run $
  spacer_n $ ruleQ $ rule "goal" [] ["max(X,Y),max(X,Z),!=(Y,Z)"]
  -- q <- ruleQ $ rule "goal" [] ["max(X,Y),max(X,Z),!=(Y,Z)"]
  -- queue %= (Q.insert q)
  -- replicateM_ 10 spacer


-- g = runFreshMT $ bmc $ rule "goal" [] ["max(X,Y)"]

-- check :: Symbolic SBool -> IO SatResult
-- check = satWith (z3 { verbose = True })


-- -- number of free vars, names for vars
-- data Rule = Rule (Int,[Text]) Term





-- -- can be infinite
-- data Enumerator = CompositeRule [(Text,[Rule])]
--           -- just any var in the env
--           -- TODO: select by type or something
--           | VarRule
--   deriving (Eq, Hashable) via PtrEq Rule


-- data Node = Var Int | Fn Text [Node]


-- -- need to do predicate ic3 or reachability graph
-- -- (to deal w/ recursive functions (definition of e.g. sort)


-- -- get_interpolant :: Node -> Map Text [Pred]
  
main = print "Hello, World!"

-- could do synthesis by spacer by making predicates that are just
-- the grammar rules (a big disjunction)?





-- could maybe for now avoid recursive specs?
-- & use predicates and/or quantifiers?

-- should think about how to handle quanfitiers in auxillary facts (/properties of functions) anyways

















