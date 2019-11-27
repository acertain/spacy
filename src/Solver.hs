-- solver interface functions (SimpleSMT wrapper)
module Solver where

import qualified SimpleSMT as S
import SExpr
import SMT
import Unbound.Generics.LocallyNameless

sexpr2smtexpr :: SExpr -> S.SExpr
sexpr2smtexpr (A n) = S.Atom $ show n
sexpr2smtexpr (B x) = S.Atom x
sexpr2smtexpr (L l) = S.List $ fmap sexpr2smtexpr l


declare' :: MonadIO m => S.Solver -> SExpr -> Name SExpr -> m ()
declare' s ty n = (liftIO $ S.declare s (show n) $ sexpr2smtexpr ty) >> pure ()

declareVars' :: MonadIO m => S.Solver -> [(SExpr,Name SExpr)] -> m ()
declareVars' s vs = for_ vs (uncurry (declare' s))

assert' :: MonadIO m => S.Solver -> SExpr -> m ()
assert' s x = liftIO $ S.assert s $ sexpr2smtexpr x


scope' :: MonadIO m => S.Solver -> m a -> m a
scope' s x = do
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
