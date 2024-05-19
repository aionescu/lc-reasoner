module LC.Syntax.DeBruijn where

import Data.Function(on)
import Data.Map.Strict(Map)
import Data.Map.Strict qualified as M

import LC.Syntax.Named

-- For the purposes of readiness/equivalence/similarity, we have to compute whether
-- an expression is in normal form, respectively whether two expressions are α-equivalent
-- or αβ-equivalent. To do this reliably (and efficiently), we first convert the the
-- expressions to De Bruijn indices, then reduce them using normalization-by-evaluation.

-- The DeBruijn-based syntax is never exposed to the student, it's only used internally
-- for checking equivalences and normal forms.

-- DeBruijn-indexed expressions
data DBExpr
  = DBVar Int
  | DBFree Ident -- For variables that were free in the top-level expression, e.g. the 'y' in '(λx. x) y'
  | DBApp DBExpr DBExpr
  | DBLam DBExpr
  deriving stock (Eq, Show, Read)

-- Converting from named representation to DeBruijn
deBruijn :: Expr -> DBExpr
deBruijn = go M.empty
  where
    go :: Map Ident Int -> Expr -> DBExpr
    go env (Var v) =
      case env M.!? v of
        Nothing -> DBFree v
        Just v -> DBVar v
    go env (App f a) = DBApp (go env f) (go env a)
    go env (Lam v e) = DBLam $ go (M.insert v 0 $ succ <$> env) e

-- NbE algorithm adapted from the following sources:
-- https://davidchristiansen.dk/tutorials/implementing-types-hs.pdf
-- https://github.com/RiscInside/LanguageEtudes/blob/main/ocaml/nbe.ml

type Env a = [a]

data Val
  = VLam (Env Val) DBExpr
  | VNeu Neutral

data Neutral
  = NVar Int
  | NFree Ident
  | NApp Neutral Val

eval :: Env Val -> DBExpr -> Val
eval env (DBVar v) = env !! v
eval _env (DBFree v) = VNeu $ NFree v
eval env (DBLam e) = VLam env e
eval env (DBApp f a) = apply (eval env f) (eval env a)

apply :: Val -> Val -> Val
apply (VLam env e) a = eval (a : env) e
apply (VNeu neu) a = VNeu (NApp neu a)

quote :: Int -> Val -> DBExpr
quote vars (VNeu (NVar lvl)) = DBVar (vars - lvl - 1)
quote _vars (VNeu (NFree v)) = DBFree v
quote vars (VNeu (NApp f a)) = DBApp (quote vars $ VNeu f) (quote vars a)
quote vars (VLam env e) = DBLam $ quote (vars + 1) $ eval (VNeu (NVar vars) : env) e

normalize' :: DBExpr -> DBExpr
normalize' = quote 0 . eval []

-- For 'similarity'
αEquiv' :: Expr -> Expr -> Bool
αEquiv' = (==) `on` deBruijn

-- For 'equivalence'
αβEquiv' :: Expr -> Expr -> Bool
αβEquiv' = (==) `on` normalize' . deBruijn

-- For 'ready'
isNormalForm' :: Expr -> Bool
isNormalForm' (deBruijn -> e) = e == normalize' e
