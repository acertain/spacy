{-# LANGUAGE DerivingVia, ScopedTypeVariables, UndecidableInstances, ViewPatterns, TemplateHaskell, GeneralizedNewtypeDeriving, NoMonoLocalBinds, PatternSynonyms #-}
module Main where

import Unbound.Generics.LocallyNameless
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



-- TODO: see what z3's spacer.ground_pobs does
-- (slides say to turn it off for spacer)


-- import Language.SMTLib2.Debug
-- import Language.SMTLib2.Pipe
-- import Language.SMTLib2


-- import Data.SBV
-- import qualified Data.SBV.List as L

-- SVar to just to make conversion to smt easier
data Term = Var (Name Term) | Constr String [Term] | SExpr (Ignore SExpr)
  -- | SVar (Ignore (Name SExpr))
  deriving (Show, Generic, Data, Eq)
newtype Clause = Clause (Bind [Name Term] [(Rule,[Term])])
  deriving (Show, Generic, Data)



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

sexpr2smtexpr :: SExpr -> S.SExpr
sexpr2smtexpr (A n) = S.Atom $ show n
sexpr2smtexpr (B x) = S.Atom x
sexpr2smtexpr (L l) = S.List $ fmap sexpr2smtexpr l

data Query = Query {
  _queryLvl :: Int,
  _queryRule :: Rule,
  -- _queryP :: Bind [Name SExpr] SExpr
  _queryArgs :: [Term],
  -- TODO: this is bad w/ mbp (need to not project vars mentioned in R)
  -- so we should just have canonical vars for the args? or store vars in queryArgs
  -- should instead use special vars for args & use equality etc?
  -- i think z3 does this?? TODO: look at z3's mk_pob / formula_o2n

  -- query is exists xs. P[xs] and R(*args[xs])
  -- invariant: all vars in args or P must be in xs
  -- currently these are delcared every query, but eventually we're going
  -- to keep them declared & mb keep (part of?) queryP in the solver or something??
  -- list of (ty,var)
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

data MState = MState {
  _queue :: Q.MinQueue Query,
  -- overapprox: facts true about the i depth unfolding of the rule
  _sigma :: HashMap Rule (Bind [Name SExpr] (IntMap SExpr)),
  -- underapprox: implies rule
  -- (forall args. reach(args) => rule(args))
  _rho :: HashMap Rule F,
  _solver :: S.Solver
}


makeLenses ''MState

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

-- TODO: remove this, as it's unused (or replace it with a version that gets to choose the variable naming?)
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
-- 
-- TODO: return list of new vars used instead of declaring them?
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

unfold' :: forall m. (Fresh m, Declare m) => (Rule -> [Term] -> m SExpr) -> Clause -> m SExpr
unfold' strat (Clause cls) = do
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
              


bmc :: Rule -> M SExpr
bmc r = unroll 10 r []
  where
    unroll :: Int -> Rule -> [Term] -> M SExpr
    unroll 0 _ _ = pure $ B "false"
    unroll k r args = unfold (unroll (k-1)) r args


ppValues :: HashMap String S.Value -> Doc
ppValues = P.vsep . fmap (\(k, v) -> P.cyan (P.text k <> " = ") <> f v) . itoList where
  f (S.Other e) = ppSExpr $ g e
  f x = P.text $ show x
  g (S.Atom x) = B x
  g (S.List l) = L $ fmap g l


rule_children :: Rule -> [Rule]
rule_children = nub . toListOf template

-- TODO: use StateT

declareVars :: [(SExpr,Name SExpr)] -> M ()
declareVars vs = for_ vs (uncurry declare)

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

data SMTResult = Sat (HashMap String S.Value) | Unsat | Unknown
  deriving (Eq)

_Sat :: Traversal' SMTResult (HashMap String S.Value)
_Sat f (Sat x) = Sat <$> f x
_Sat _ x = pure x

check :: S.Solver -> [Name SExpr] -> IO SMTResult
check s vs = S.check s >>= \case
  S.Sat -> Sat . fromList <$> S.getConsts s (fmap show vs)
  S.Unsat -> pure Unsat
  S.Unknown -> pure Unknown

  

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
        (xs,dvs) <- runDeclaredVarsT $ flip runStateT mempty $ do
          q <- unfold' (cook (lvl-1)) cls
          print q
          liftIO $ do
            S.assert s $ sexpr2smtexpr q
            S.assert s $ sexpr2smtexpr $ _queryP query
          pure q
        let vs = dvs ++ _queryExists query
        r <- liftIO $ approx_maxsat s (fmap A $ toListOf (_2 . traverse . traverse . _1) xs) $ check s $ fmap snd vs
        -- liftIO $ print $ ppValues model
        pure (r, xs, vs, cls)
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
             true_in_model model v = anyOf (ix (show v)) (== S.Bool True) model
             als = filter (allOf (lensProduct _1 (_2 . _2)) (\(model, as) -> all (true_in_model model) $ concat $ toList as)) ls'
            --  is_x :: (S.Value -> Bool) -> HashMap String S.Value -> Name SExpr -> Bool
            --  is_x p model var = anyOf (ix (show var)) p model
            --  g = fmap (\t -> (t, filter (not . is_x (== S.Bool True) (t ^. _1) . snd) (t ^. _))) ls'
      in 
      if (not . null) als then do
        -- TODO: should make rho = branch that was reachable
        let cls = als ^?! _head . _4
        print $ P.green "Reachable with no assumptions"
        avs <- ruleVars rule
        -- (avs,_) <- unbind (query ^. queryRule . ruleBody)
        -- (ua,uvs) <- runDeclaredVarsT $ unfold (\x y -> liftS $ under x y) rule $ fmap Var $ coerce avs
        (ua,uvs) <- runDeclaredVarsT $ unfold (\x y -> liftS $ under x y) rule $ fmap Var $ coerce avs
        -- TODO: is this right
        -- should minimize the exists here
        print ua
        rho . at (_queryRule query) .= Just (bind avs $ sExists uvs ua)
        queue .= queue'
      else do
        print $ P.yellow "Reachable with assumptions: " <> P.text (show $ fmap (^. _2 . _2) ls')
        -- TODO: should we only queue first so that later branches can use improved sigmas?
        for_ ls' $ \(model, (q, as), vs, cls) -> do
          -- TODO: mb have type RuleTag = (Rule, Int) for nth occ of rule
          -- & use that to simplify this stuff
          let (child_rule,(_,child_args)) = as ^@?! (itraversed <. traverse . filtered (not . true_in_model model . fst))
          -- TODO: need to cook a version with sigma/rho chosen by assumptions & vars named according to model
          -- or get it by simplification?
          -- let (child_rule,args) = as
          --       & singular (itraversed <. traverse . filtered (not . true_in_model model)) %%@~ _
          -- let (child_rule,rhos_model) = as
          --       & fmap reverse
          --       & (traverse . traverse) %~ (Just . true_in_model model)
          --       & singular (itraversed <. traverse . filtered (== Just False)) %%@~ (\r _ -> (r, Nothing))
          -- ((qr',(_,Just child_args)),dvs') <- runDeclaredVarsT $ flip runStateT (rhos_model, Nothing) $ scope $ unfold' (cook_with_map (lvl-1)) cls
          -- print qr'
          queue %= (Q.insert $ Query {
            _queryLvl = lvl - 1,
            _queryRule = child_rule,
            _queryArgs = child_args,
            _queryExists = vs,
            _queryP = sAnd [q, _queryP query],
            -- TODO: this is wrong :/, need model of dvs'
            _queryModel = model
          })
          pure ()
    -- undefined
    --     else if lvl <= 0 then
    --       -- TODO: is this in the right place? should it be <= 1?
    --       -- TODO: is this reachable(is this check redundant?) if sigma -1 = false ?
    --       -- TODO: report unknown
    --       queue .= queue'
  Nothing -> pure ()
  where
    -- each rule has a list of it's instances
    -- for each instance, we store args & bool var which signals if underapprox was satisfied by model (in which case don't need to query that rule)
    cook :: Int -> Rule -> [Term] -> StateT (HashMap Rule [(Name SExpr,[Term])])
     (DeclaredVarsT M) SExpr
    cook lvl r ys = do
      a <- fresh $ s2n (r ^. ruleName)
      liftS $ declare (B "Bool") a
      o <- liftS $ over lvl r ys
      u <- liftS $ under r ys
      at r . non [] %= ((a,ys):)
      pure $ sAnd [o, L [B "=", A a, u]]

    -- cook_with_map :: Model -> Name SExpr -> Int -> Rule -> [Term] -> StateT (HashMap Rule [Name SExpr], Maybe [Term]) (DeclaredVarsT M) SExpr
    -- cook_with_map m qr lvl r ys = do
    --   Just (x:xs) <- use (_1 . at r)
    --   _1 . at r .= Just xs
    --   if x == qr then do
    --     print ys
    --     _2 .= Just ys
    --   else case modelVal m x of
    --     S.Bool True -> do
    --       -- TODO: should we just do under?
    --       o <- liftS $ over lvl r ys
    --       u <- liftS $ under r ys
    --       pure $ sAnd [u, o]
    --     S.Bool False -> liftS $ over lvl r ys
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
  let st = MState mempty mempty mempty s
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
  replicateM_ 20 spacer
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

















