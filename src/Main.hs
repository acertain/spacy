{-# LANGUAGE DerivingVia, ScopedTypeVariables, UndecidableInstances, ViewPatterns, TemplateHaskell, GeneralizedNewtypeDeriving, NoMonoLocalBinds, PatternSynonyms #-}
module Main where

import Unbound.Generics.LocallyNameless
import qualified Unbound.Generics.LocallyNameless.Bind
import qualified Data.IntMap.Internal
import qualified Data.IntMap.Lazy as IM
import Data.Data.Lens
import Prelude hiding (cls, liftM)
import qualified SimpleSMT as S
import qualified Text.PrettyPrint.ANSI.Leijen as P
import Debug.Trace
import qualified Data.PQueue.Min as Q
import Control.Exception
import GHC.Stack
import SExpr
import SMT
import Rule
import Solver
import System.Mem.Weak
import Data.HashSet (HashSet)
import Control.DeepSeq

-- TODO: switch away from unbound?
-- really want a version without the semi-mandatory handling of free vars + freshening (or with it easier to disable)


-- unbind, but without freshening (just uses names as they were bound)
-- TODO: use lunbind instead?
unbindish :: (Alpha p, Alpha t) => Bind p t -> (p, t)
unbindish (Unbound.Generics.LocallyNameless.Bind.B p t) = (p, open initialCtx (nthPatFind p) t)


type F = Bind [Name SExpr] SExpr

deriving instance Generic a => Generic (IntMap a)
instance (Generic a, Alpha a) => Alpha (IntMap a)
instance (Generic a, Subst b a) => Subst b (IntMap a)

instance Hashable (Name a)


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

-- TODO: do a solver per clause



-- TODO: abstraction for growable sets (& lists etc) with associated cursors & diff since cursor (mb where diff can say reset/be partial?)

data ClauseState = ClauseState {
  _csSolver :: S.Solver,
  _csChildRules :: HashMap (Name SExpr) (Rule,[Term],[Name SExpr],IntMap Int),
  _csVars :: [Name SExpr],
  -- just the contraints from the clause, instantiated
  _csConstraints :: SExpr
} deriving (Show)



data PredState = PredState {
  _psPredArgs :: [Name SExpr],
  _psClauses :: [ClauseState],
  -- (assumption var, reach fact)
  _psRho :: [(Name SExpr, SExpr)],
  -- map lvl => facts
  _psSigma :: IntMap [SExpr]
} deriving (Show)

instance Show S.Solver where show _ = ""

data MState = MState {
  _queue :: Q.MinQueue Query,
  -- overapprox: facts true about the i depth unfolding of the rule
  _sigma :: HashMap Rule (Bind [Name SExpr] (IntMap SExpr)),
  -- underapprox: implies rule
  -- (forall args. reach(args) => rule(args))
  _preds :: HashMap Rule PredState
  -- _solver :: S.Solver
}


makeLenses ''MState
makeLenses ''PredState
makeLenses ''ClauseState

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




inst :: (HasCallStack, Subst a b, Typeable a, Alpha b, Fresh m) => Bind [Name a] b -> [a] -> m b
inst b l = do
  (vs,c) <- unbind b
  when (length l /= length vs) $
    error $ "inst: length mismatch: " <> show (length l) <> " /= " <> show (length vs)
  pure $ substs (zip vs l) c

ppValues :: HashMap String SExpr -> Doc
ppValues = P.vsep . fmap (\(k, v) -> P.cyan (P.text k <> " = ") <> ppSExpr v) . itoList


rule_children :: Rule -> [Rule]
rule_children = nub . toListOf template

-- TODO: use StateT



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


make_solver :: MonadIO m => m S.Solver
make_solver = liftIO $ do
  l <- S.newLogger 0
  s <- S.newSolver "z3" ["-smt2","-in"] $ Just l
  S.declareDatatype s "Tm" [] [
    ("Tm_int", [("tm_int", S.tInt)]),
    ("Tm_tree", [("tm_head", S.Atom "String"), ("tm_children", S.List [S.Atom "List", S.Atom "Tm"])])]
  addFinalizer s (S.stop s >> pure ())
  pure s

init_clause :: [Name Term] -> Clause -> M ClauseState
init_clause hvs (Clause cls) = do
  s <- make_solver
  declare' s (B "Int") $ s2n "lvl"
  for_ hvs (declare' s (B "Tm") . coerce)
  (rvs,(cs,rhs)) <- pure $ unbindish cls
  for_ rvs (declare' s (B "Tm") . coerce)
  (m,rhs') <- fmap sequenceA $ ifor rhs (f s)
  assert' s $ sAnd (cs:rhs')
  pure $ ClauseState {
    _csVars = coerce rvs,
    _csSolver = s,
    _csChildRules = m,
    _csConstraints = cs
  } where
    f s i (r, xs) = do
      let n = s2n $ "cls_" ++ show i
      declare' s (B "Bool") n
      assert' s $ sImplies (A n) $ sImplies (L [B "<=", B "lvl", B "0"]) $ B "false"
      pure (mempty & at n .~ Just (r, xs, mempty, mempty), A n)




init_pred :: Rule -> M PredState
init_pred r = do
  let (vs,cls) = unbindish (_ruleBody r)
  cs <- for cls (init_clause vs)
  pure $ PredState {
    _psPredArgs = coerce vs,
    _psClauses = cs,
    _psRho = mempty,
    _psSigma = mempty
  }

-- TODO: could do things other than solver per clause
-- e.g. one solver, keep however many instances of each pred's sigma/rho is needed
-- to run queries, use equalities to activate them
-- or solver per pred
-- but solver per pred is much simpler, so the plan is to do it for now 
-- & think about how to do one solver efficiently or like Andorra-style execution



pre_query :: Int -> PredState -> ClauseState -> M ClauseState
pre_query lvl ps cs =
  iforOf (csChildRules .> itraversed) cs $ \a ro@(r, xs, rfs, ss) -> do
    use (preds . at r) >>= \case
      Nothing -> pure ro
      Just rs -> do
        rfs' <- case rs ^? psRho . _head of
          Just (t',f) ->
            -- TODO: need a copy of t per instance of r
            -- this is a hack? should mb keep map back to psRho & use fresh vars here?
            let t = s2n (show t' ++ show a) in
            if t `elem` rfs then pure (t:delete t rfs)
            else do
              let f' = substs (zipWith (\v x -> (v, tm2expr x)) (rs ^. psPredArgs) xs) f
              declare' s (B "Bool") t
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
  where s = cs ^. csSolver
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

-- so like the unfold gives you back an `Model -> a`
-- given how to combine a's with ors (given which branch is true) and ands and rules?
-- then can impl unfold by either evaluating both branches of an or in the model
-- or by using intermediate vars & checking their val in the model

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
  ps <- ruleState rule
  cls <- for (ps ^. psClauses) (pre_query (lvl-1) ps)
  preds . at rule .= Just (ps & psClauses .~ cls)
  r <- for cls $ \cs -> do
    let s = cs ^. csSolver
    let rs = cs ^. csChildRules
    let as = fmap fst $ itoList rs
      -- TODO: do maxsmt here 
    -- max prod_j=conj [rho_ij!=1]*p(A_ij)
    -- or max prod_j=conj max([rho_ij=1],p(A_ij))
    -- or look at what z3 does
    scope' s $ do
      assert' s (sEq (B "lvl") (B $ show lvl))
      declareVars' s $ _queryExists query
      assert' s prop
      -- TODO: need to do maxsmt here for termination
      -- can be according to any order on rhos i think (which rhos are satisfied)
      -- (obvious one is max lexicographic combination of number satisfied then left to right)
      liftIO (check' s) >>= \case
        Unsat -> pure $ Just False
        Sat m -> do
          -- the child rules the model depends on
          let as' = filter (true_in_model m) as
          -- look for a child rule with a rho not satisfied
          -- TODO: mb choose here randomly or do all or?
          case find (\v -> let x = rs ^?! ix v . _3 in null x || not (true_in_model m $ head x)) as' of
            Nothing -> do
              print $ P.green "Reachable with no assumptions, model:"
              ua <- sAnd . ((cs ^. csConstraints):) <$> for (itoList rs) (\(a,(r, args, _, _)) -> g rs a r args)
              a_name <- fresh $ s2n "a_"
              let uvs = zip (repeat $ B "Tm") (cs ^. csVars)
              preds . at rule . _Just . psRho %= ((a_name, sExists uvs ua):)
              print m
              -- TODO: update rho
              pure $ Just True
            Just k -> if lvl < 0 then
                error "At lvl < 0 but reachable with assumptions, this is an internal error"
              else do
              let x = rs ^?! ix k
              -- TODO: need to impl the q3 paper (instantiating skolems i think)
              -- TODO: need to not use quantified lemmas when generating query (just use instances) i think
              -- at least that's what z3 does
              print $ P.yellow "Reachable with assumptions, querying " <> P.text (show x)
              -- TODO: need to do capture avoidant naming/substn at various points here
              -- FIXME: using rs here is wrong b/c it doesn't have prims
              q <- sAnd . ((cs ^. csConstraints):) <$> for (itoList rs) (\(a,(r, args, _, _)) -> f lvl m rs a r args)
              print q
              let xs = cs ^. csVars
              let argvars = fmap (\i -> s2n ("var!" ++ show i)) [1..]
              let (qvs,q') = pMbp' m (fmap (B "Tm",) xs ++ _queryExists query) $ sAnd (q:zipWith sEq (fmap A argvars) (fmap tm2expr (x ^. _2)))
              rule_ps <- ruleState (x ^. _1)
              print rule_ps
              let ruleargs = rule_ps ^. psPredArgs
              let q'' = substs (zip argvars $ fmap A ruleargs) q'
              -- TODO: need to add sks to model i think
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
                _queryExists = sks,
                _queryP = q3,
                -- _queryExists = [],
                -- _queryP = sExists sks q3,
                -- _queryP = sExists qvs q'',
                _queryModel = m
              })
              pure Nothing
  if all (== Just False) r then do
    let f = sNot $ pMbp (_queryModel query) (_queryExists query) prop
    print $ P.red "Unreachable, updating sigma with:"
    print f
    preds . ix rule . psSigma . at lvl . non [] %= (++ [f])
    pure $ Just False
  else if any (== Just True) r then do
    pure $ Just True
  else pure Nothing
    where
      -- true_in_model model v = anyOf (ix (show v)) (== B "true") model
      true_in_model m v = case modelVal m (A v) of
        B "true" -> True
        B "false" -> False
        _ -> undefined
      f lvl m rls a r xs = do
        let rs = rls ^?! ix a . _3 
        ps <- ruleState r
        let c = if has _head rs && true_in_model m (head rs) then
                  fromJust $ lookup (head rs) (ps ^. psRho)
                else
                  sAnd $ concat $ toList $ snd $ IM.split (lvl-1) (ps ^. psSigma)
        -- print $ P.cyan "Approx for"
        -- print r
        -- print c
        pure $ substs (zipWith (\n v -> (n, tm2expr v)) (ps ^. psPredArgs) xs) c
      g rls a r xs = do
        let rs = rls ^?! ix a . _3 
        ps <- ruleState r
        pure $ fromJust $ lookup (head rs) (ps ^. psRho)
  --   --  print ls


spacer' = (Q.minView <$> use queue) >>= \case
    Just (query, queue') -> do
      r <- run_query query
      when (isJust r) (queue .= queue')
    Nothing -> pure ()

run m = do
  -- l <- S.newLogger 1
  -- s <- S.newSolver "z3" ["-smt2","-in"] $ Just l
  let st = MState mempty mempty mempty
  runFreshMT $ flip runStateT st $ runM m



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

















