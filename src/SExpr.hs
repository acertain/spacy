{-# LANGUAGE ViewPatterns #-}
module SExpr where

import Unbound.Generics.LocallyNameless
import qualified Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless.Ignore
import qualified Text.PrettyPrint.ANSI.Leijen as P
import Data.Data.Lens


-- TODO: rename A -> V
data SExpr = A (Name SExpr) | B String | L [SExpr]
  deriving (Generic, Data, Eq)

instance Subst SExpr SExpr where
  isvar (A x) = Just $ SubstName x
  isvar _ = Nothing

instance Alpha SExpr

deriving instance Data a => Data (Ignore a)
deriving instance Eq a => Eq (Ignore a)


deriving instance Data a => Data (Name a)
deriving instance (Data k, Data v) => Data (Bind k v)

ppSExpr :: SExpr -> Doc
ppSExpr = g . inline_linear_lets where
  g (B a) = P.text a
  g (A a) = P.text $ show a
  g (L [a]) = g a
  g (L [B "Tm_int",i]) = g i
  g (L [B "Tm_tree",B (strip_quotes -> Just n),unlist -> Just l]) = P.text n <> "(" <> intercalate "," (fmap g l) <> ")"
  g (L (l:ls)) = P.hang 2 ("(" <> g l <> " " <> (P.sep $ fmap g ls) <> ")")

  unlist (B "nil") = Just []
  unlist (L [B "insert", x, y]) = (x :) <$> unlist y
  unlist x | trace (show x) True = Nothing

  strip_quotes x | head x == '"' && last x == '"' = Just $ tail $ init x
                 | otherwise = Nothing

  inline_linear_lets = rewriteOf uniplate r where
    varsOf tm = (toListOf template tm :: [String])

    r (L [B "let", L [L [B v, x]], b]) | isUniqVar v b && (v `notElem` varsOf x) = Just $ rewriteOf uniplate (subst v x) b
    r _ = Nothing

    subst v y (B w) | v == w = Just y
    subst _ _ _ = Nothing

    isUniqVar u tm = length (elemIndices u $ varsOf tm) <= 1

instance Show SExpr where
  showsPrec _ = P.displayS . P.renderSmart 1 100 . ppSExpr