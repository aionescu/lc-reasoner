module LC.Reasoner where

import Ideas.Common.Library
import Ideas.Main.Default

import LC.Syntax

-- This module contains the definition of the Domain Reasoner,
-- including rule and strategy definitions.

-- Named with a ' to avoid clashing with the Exercise field name.
examples' :: Examples Expr
examples' = examplesWithDifficulty $ easy <> medium <> hard
  where
    easy =
      (Easy,) . parseKnown <$>
      [ "(λx. x) y"
      , "(λy x. f x) y"
      , "(λx. x) (λy. y)"
      , "(λx y. y x) z w"
      , "(λx. x x) (λx. x)"
      ]

    medium =
      (Medium,) . parseKnown <$>
      [ "(λx y. y) (λx. y)"
      , "(λx. x ((λy. y) z)) w"
      , "(λf x. f (f x)) x"
      , "(λx. f ((λy. y) x) x) y"
      , "(λf x y. f (f x y)) x y"
      , "(λf. (λx. f (f x)) (λx. f (f x))) x"
      , "(λx. x x) ((λy. y y) z)"
      , "(λa. a) (λx. (λy. y) z ((λx. x) w))"
      ]

    hard =
      (Difficult,) . parseKnown <$>
      [ "(λZ S. S (S Z)) (λf z. z) (λn f z. f (n f z))" -- Evaluate 2 in Church numerals
      , "(λZ S +. + (S (S Z)) (S (S Z))) (λf z. z) (λn f z. f (n f z)) (λm n f z. m f (n f z))" -- Evaluate 2 + 2 in Church numerals
      , "(λZ S *. * (S (S (S Z))) (S (S Z))) (λf z. z) (λn f z. f (n f z)) (λm n f z. m (n f) z)" -- Evaluate 3 * 2 in Church numerals
      , "(λZ S + *. + (S Z) (* (S (S Z)) (S (S (S Z))))) (λf z. z) (λn f z. f (n f z)) (λm n f z. m f (n f z)) (λm n f z. m (n f) z)" -- Evaluate 1 + 2 * 3 in Church numerals
      , "(λx. x x) (λ💀. 💀 💀)" -- Parser accepts (almost) anything as identifiers :)
      , "λf. (λx. x x) (λx. f (x x))" -- Y combinator
      ]

-- Apply a β-reduction, if no α-renaming is needed.
βRule :: Rule Expr
βRule =
  describe "β-reduce" $
    makeRule "lc.beta" \case
      App (Lam v e) a -> trySubst v a e
      _ -> Nothing

-- If a β-reduction fails due to capturing during substitution,
-- α-rename the subterm that caused the failure.
αRule :: Rule Expr
αRule =
  describe "α-rename" $
    makeRule "lc.alpha" \case
      App (Lam v e) a | Just e' <- αRename v a e -> Just $ App (Lam v e') a
      _ -> Nothing

-- Buggy β-reduction which doesn't avoid variable capture, thus
-- changing the meaning of the expression.
βRuleBuggy :: Rule Expr
βRuleBuggy =
  describe "β-reduce (buggy)" $
    setBuggy True $
      makeRule "lc.beta.buggy" \case
        App (Lam v e) a | Nothing <- trySubst v a e -> Just $ substBuggy v a e
        _ -> Nothing

-- Apply an η-reduction, if possible.
ηRule :: Rule Expr
ηRule =
  describe "η-reduce" $
    makeRule "lc.eta" \case
      Lam v (App f (Var v')) | v == v', v `notFreeIn` f -> Just f
      _ -> Nothing

-- Buggy η-reduction that reduces 'λx. f x' to 'f' even if 'x' is free in 'f'.
ηRuleBuggy :: Rule Expr
ηRuleBuggy =
  describe "η-reduce (buggy)" $
    setBuggy True $
      makeRule "lc.eta.buggy" \case
        Lam v (App f (Var v')) | v == v', v `freeIn` f -> Just f
        _ -> Nothing

-- As per https://en.wikipedia.org/wiki/Lambda_calculus#Reduction_strategies
-- Normal order: "The leftmost outermost redex is reduced first."
-- Appliative order: "The leftmost innermost redex is reduced first."

-- The 'outermost' and 'innermost' combinators do exactly what we need,
-- so the strategies are easy to define.

normalOrderStrategy :: LabeledStrategy (Context Expr)
normalOrderStrategy =
  label "lc.norm" $
    outermost (liftToContext $ βRule |> αRule |> ηRule)
    |> outermost (liftToContext $ βRuleBuggy .|. ηRuleBuggy)

applicativeOrderStrategy :: LabeledStrategy (Context Expr)
applicativeOrderStrategy =
  label "lc.app" $
    innermost (liftToContext $ βRule |> αRule |> ηRule)
    |> innermost (liftToContext $ βRuleBuggy .|. ηRuleBuggy)

normalForms :: [(String, String, Expr  -> Bool)]
normalForms =
  [ ("nf", "normal form", isNormalForm)
  , ("hnf", "head normal form", isHeadNormalForm)
  , ("whnf", "weak-head normal form", isWeakHeadNormalForm)
  ]

reductionOrders ::[(String, String, LabeledStrategy (Context Expr))]
reductionOrders =
  [ ("norm", "normal order", normalOrderStrategy)
  , ("app", "applicative order", applicativeOrderStrategy)
  ]

mkExercise :: (String, String, Expr -> Bool) -> (String, String, LabeledStrategy (Context Expr)) -> Exercise Expr
mkExercise (nfId, nfName, nfPredicate) (orderId, orderName, orderStrategy) =
  emptyExercise
  { exerciseId    = describe
                      ("Reduce a λ-term to " <> nfName <> ", using " <> orderName <> " reduction")
                      (newId $ "lc." <> nfId <> "." <> orderId)
  , status        = Experimental
  , strategy      = orderStrategy
  , prettyPrinter = prettyPrintExpr
  , navigation    = termNavigator
  , parser        = parseExpr
  , equivalence   = withoutContext αβηEquiv
  , similarity    = withoutContext αEquiv
  , ready         = predicate nfPredicate
  , examples      = examples'
  }

exercises' :: [Exercise Expr]
exercises' = mkExercise <$> normalForms <*> reductionOrders

reasoner :: DomainReasoner
reasoner =
  describe "Domain reasoner for λ-calculus"
    (newDomainReasoner "lc")
    { exercises = Some <$> exercises'
    , services  = metaServiceList reasoner <> serviceList
    }

runDomainReasoner :: IO ()
runDomainReasoner = defaultMain reasoner
