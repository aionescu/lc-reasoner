module LC.Syntax.Named where

import Control.Applicative((<|>), some)
import Data.Char(isSpace)
import Ideas.Common.Library hiding (apply, many)
import Ideas.Utils.Parsing hiding ((<|>))
import Data.Set(Set)
import Data.Set qualified as S
import Data.Maybe (fromMaybe)
import Data.Function(on)

-- This module contains the λ-calculus AST and associated definitions:
-- parser and pretty-printer, IsTerm instance, substitution and free vars etc.

-- AST definition

type Ident = String

data Expr
  = Var Ident
  | App Expr Expr
  | Lam Ident Expr
  deriving stock (Eq, Ord, Show, Read)

-- Parser & pretty-printer

parseExpr :: String -> Either String Expr
parseExpr = parseSimple expr
  where
    ident :: Parser String
    ident = some $ satisfy \c -> c `notElem` "λ\\.()" && not (isSpace c)

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

-- Try to substitute a variable in the given expression.
-- Returns Nothing if the substitution would capture a variable.
trySubst :: Ident -> Expr -> Expr -> Maybe Expr
trySubst v e (Var v')
  | v == v' = Just e
  | otherwise = Just $ Var v'
trySubst v e (App f a) = App <$> trySubst v e f <*> trySubst v e a
trySubst v e (Lam v' e')
  | v == v' = Just $ Lam v' e'
  | v' `notFreeIn` e = Lam v' <$> trySubst v e e'
  | otherwise = Nothing

-- α-rename the first subterm that would prevent substitution.
αRename :: Ident -> Expr -> Expr -> Expr
αRename v e e' = go S.empty v e e'
  where
    go :: Set Ident -> Ident -> Expr -> Expr -> Expr
    go _ _ _ (Var v) = Var v
    go all v e (App f a) = App (go all v e f) (go all v e a)
    go all v e (Lam v' e')
      | v == v' = Lam v' e'
      | v' `notFreeIn` e = Lam v' $ go (S.insert v' all) v e e'
      | otherwise = freshen (S.insert v' all) v' e'

    -- Generate a fresh name for the given λ-abstraction.
    freshen :: Set Ident -> Ident -> Expr -> Expr
    freshen all v e = Lam v' $ fromMaybe (error "freshen: Unreachable") $ trySubst v (Var v') e
      where
        v' = next all v

        next all v
          | S.notMember v all = v
          | otherwise = next all (v <> "'")

-- Substitute a variable in an expression, performing α-renaming if necessary.
substRenaming :: Ident -> Expr -> Expr -> Expr
substRenaming v e e' =
  case trySubst v e e' of
    Just e'' -> e''
    Nothing -> fromMaybe (error "substRenaming: Unreachable") $ trySubst v e $ αRename v e e'

-- Substitute a variable in the given expression.
-- This implementation doesn't consider the "freshness" condition,
-- potentially changing the meaning of the expression.
substBuggy :: Ident -> Expr -> Expr -> Expr
substBuggy v e (Var v')
  | v == v' = e
  | otherwise = Var v'
substBuggy v e (App f a) = App (substBuggy v e f) (substBuggy v e a)
substBuggy v e (Lam v' e')
  | v == v' = Lam v' e'
  | otherwise {- v' `notFreeIn` e -} = Lam v' $ substBuggy v e e' -- Oops, we captured the variable

-- Compute α-equivalence.
αEquiv :: Expr -> Expr -> Bool
αEquiv (Var v) (Var v') = v == v'
αEquiv (App f a) (App f' a') = αEquiv f f' && αEquiv a a'
αEquiv (Lam v e) (Lam v' e')
  | v == v' = αEquiv e e'
  | otherwise = αEquiv e $ substRenaming v' (Var v) e'
αEquiv _ _ = False

-- Apply one reduction step to the given term (normal order).
step :: Expr -> Maybe Expr
step Var{} = Nothing
step (App (Lam v e) a) = Just $ substRenaming v a e
step (App f a) = (`App` a) <$> step f <|> App f <$> step a
step (Lam v e) = Lam v <$> step e

-- Normalize a λ-term, taking care not to loop.
normalize :: Expr -> Expr
normalize e = go (S.singleton e) e
  where
    go seen e =
      case step e of
        Nothing -> e
        Just e'
          -- This is very slow; The "proper" way would be to convert to
          -- DeBruijn indices first, but that feels overkill for this exercise.
          | any (αEquiv e') seen -> e'
          | otherwise -> go (S.insert e' seen) e'

αβEquiv :: Expr -> Expr -> Bool
αβEquiv = αEquiv `on` normalize

-- Normal forms as per https://en.wikipedia.org/wiki/Beta_normal_form

-- See definition in LC.Syntax.DeBruijn
isNormalForm :: Expr -> Bool
isNormalForm Var{} = True
isNormalForm (App Lam{} _) = False
isNormalForm (App f a) = isNormalForm f && isNormalForm a
isNormalForm (Lam _ e) = isNormalForm e

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
