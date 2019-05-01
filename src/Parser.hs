-- a shitty parser for a subset of prolog

module Parser where

import Text.Parsix hiding (ident)
import Prelude hiding (noneOf)


ident :: Parser String
ident = some $ noneOf " ,.()"

spc = many $ oneOf " "

rhs :: Parser [Expr]
rhs = term `sepBy` (spc >> char ',' >> spc)

data Expr = Expr String [Expr]
  deriving (Show, Data)

term :: Parser Expr
term = Expr <$> ident <*> (
  maybe [] id <$> optional (char '(' *> (term `sepBy` (char ',')) <* char ')')) -- <* char '(' <*> _ *> char ')')


parseClause :: String -> [Expr]
parseClause src = case parseString (rhs <* eof) src "" of 
  Success x -> x
  Failure e -> error $ show e


-- clause :: Parser _
-- clause = (,) <$> some (noneOf " ,.()")-- <*> char '('



