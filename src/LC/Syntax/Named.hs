module LC.Syntax.Named where

import Control.Applicative((<|>), some)
import Data.Char(isLetter)
import Ideas.Common.Library hiding (many)
import Ideas.Utils.Parsing hiding ((<|>))
import Data.Set(Set)
import Data.Set qualified as S
import Data.Maybe (fromMaybe)

-- This module contains the λ-calculus AST and associated definitions:
-- parser and pretty-printer, IsTerm instance, substitution and free vars etc.

-- AST definition

type Ident = String

data Expr
  = Var Ident
  | App Expr Expr
  | Lam Ident Expr
  deriving stock (Eq, Show, Read)

-- Parser & pretty-printer

parseExpr :: String -> Either String Expr
parseExpr = parseSimple expr
  where
    ident :: Parser String
    ident = (:) <$> satisfy (\c -> isLetter c && c /= 'λ') <*> many (alphaNum <|> oneOf ['_', '\''])

    parens :: Parser a -> Parser a
    parens = between (char '(' *> spaces) (char ')' *> spaces)

    lam =
      flip (foldr Lam)
      <$> (oneOf ['λ', '\\'] *> spaces *> some (ident <* spaces) <* (string "->" <|> string ".") <* spaces)
      <*> expr

    exprSimple = Var <$> ident <|> parens expr
    exprApp = chainl1 (exprSimple <* spaces) (pure App)
    expr = exprApp <|> lam

parseKnown :: String -> Expr
parseKnown = either (error . ("parseKnown: " <>)) id . parseExpr

prettyPrintExpr :: Expr -> String
prettyPrintExpr = go False
  where
    go _ (Var v) = v
    go nested (App f a) = parens nested $ go True f <> " " <> go True a
    go nested (Lam v e) = parens nested $ "λ" <> v <> ". " <> go False e

    parens False s = s
    parens True s = "(" <> s <> ")"

-- Free vars & substitutions

free :: Expr -> Set Ident
free (Var v) = S.singleton v
free (App f a) = free f <> free a
free (Lam v e) = S.delete v $ free e

notFreeIn :: Ident -> Expr -> Bool
notFreeIn v = S.notMember v . free

subst :: Ident -> Expr -> Expr -> Maybe Expr
subst v e (Var v')
  | v == v' = Just e
  | otherwise = Just $ Var v'
subst v e (App f a) = App <$> subst v e f <*> subst v e a
subst v e (Lam v' e')
  | v == v' = Just $ Lam v' e'
  | v' `notFreeIn` e = Lam v' <$> subst v e e'
  | otherwise = Nothing

-- α-rename the first subterm that would prevent substitution.
-- This algorihtm follows the same structure as substitution,
-- but doesn't actually substitute.
substRenaming :: Ident -> Expr -> Expr -> Expr
substRenaming v e e' = go S.empty v e e'
  where
    go :: Set Ident -> Ident -> Expr -> Expr -> Expr
    go _ _ _ (Var v) = Var v
    go all v e (App f a) = App (go all v e f) (go all v e a)
    go all v e (Lam v' e')
      | v == v' = Lam v' e'
      | v' `notFreeIn` e = Lam v' $ go (S.insert v' all) v e e'
      | otherwise = αRename (S.insert v' all) v' e'

    -- Generate a fresh name for the given λ-abstraction.
    -- The 'Set Ident' stores all variables seen so far,
    -- to prevent creating an already-existing variable.
    αRename :: Set Ident -> Ident -> Expr -> Expr
    αRename all v e = Lam v' $ fromMaybe err $ subst v (Var v') e
      where
        v' = next all v
        err = error $ "αRename: Can't substitute fresh var " <> v'

        next all v
          | S.notMember v all = v
          | otherwise = next all (v <> "'")

-- Normal forms
-- As defined in https://en.wikipedia.org/wiki/Beta_normal_form

-- See definition in LC.Syntax.DeBruijn
isNormalForm' :: Expr -> Bool
isNormalForm' Var{} = True
isNormalForm' (App Lam{} _) = False
isNormalForm' (App f a) = isHeadNormalForm f && isNormalForm' a
isNormalForm' (Lam _ e) = isHeadNormalForm e

hasNoHeadRedex :: Expr -> Bool
hasNoHeadRedex Var{} = True
hasNoHeadRedex (App f _) = hasNoHeadRedex f
hasNoHeadRedex Lam{} = False

isHeadNormalForm :: Expr -> Bool
isHeadNormalForm Var{} = True
isHeadNormalForm (App f _) = hasNoHeadRedex f
isHeadNormalForm (Lam _ e) = isHeadNormalForm e

isWeakHeadNormalForm :: Expr -> Bool
isWeakHeadNormalForm Lam{} = True
isWeakHeadNormalForm e = isHeadNormalForm e

-- IsTerm instance

varSymbol :: Symbol
varSymbol = newSymbol "Var"

appSymbol :: Symbol
appSymbol = newSymbol "App"

lamSymbol :: Symbol
lamSymbol = newSymbol "Lam"

instance IsTerm Expr where
  toTerm :: Expr -> Term
  toTerm (Var v) = unary varSymbol (TVar v)
  toTerm (App f a) = binary appSymbol (toTerm f) (toTerm a)
  toTerm (Lam v e) = binary lamSymbol (TVar v) (toTerm e)

  termDecoder :: TermDecoder Expr
  termDecoder =
    tCon1 varSymbol Var tVar
    <|> tCon2 appSymbol App termDecoder termDecoder
    <|> tCon2 lamSymbol Lam tVar termDecoder
