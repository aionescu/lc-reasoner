module LC.Reasoner where

import Ideas.Common.Library hiding (many)
import Ideas.Main.Default

import LC.Syntax.Named
import LC.Syntax.DeBruijn

-- This module contains the definition of the Domain Reasoner,
-- including rule and strategy definitions.

-- Named with a ' to avoid clashing with the Exercise field name.
examples' :: Examples Expr
examples' = examplesWithDifficulty $ easy <> medium <> hard
  where
    easy =
      (Easy,) . parseKnown <$>
      [ "(λx. x) y"
      , "(λx. x) (λy. y)"
      , "(λx y. y x) z w"
      , "(λx. x x) (λx. x)"
      ]

    medium =
      (Medium,) . parseKnown <$>
      [ "(λx y. y) (λx. y)"
      , "(λx. x ((λy. y) z)) w"
      , "(λf x. f (f x)) x"
      , "(λf x y. f (f x y)) x y"
      ]

    hard =
      (Difficult,) . parseKnown <$>
      [ "(λx y. y) (λx. y)"
      , "(λx. x ((λy. y) z)) w"
      , "(λf x. f (f x)) x"
      , "(λf x y. f (f x y)) x y"
      --, "(λx. x x) (λx. x x)" -- 💀
      ]

-- Apply a β-reduction, if no α-renaming is needed.
βRule :: Rule Expr
βRule =
  describe "β-reduce" $
    makeRule "lc.beta" \case
      App (Lam v e) a -> subst v a e
      _ -> Nothing

-- If a β-reduction fails due to capturing during substitution,
-- α-rename the subterm that caused the failure.
αRule :: Rule Expr
αRule =
  describe "α-rename" $
    makeRule "lc.alpha" \case
      App (Lam v e) a | Nothing <- subst v a e -> Just $ App (Lam v $ substRenaming v a e) a
      _ -> Nothing

normalOrderStrategy :: LabeledStrategy (Context Expr)
normalOrderStrategy =
  label "Normal order reduction"
  $ outermost $ liftToContext $ βRule |> αRule

-- This is wrong, it should be 'rightmost', but that's not in the library.
applicativeOrderStrategy :: LabeledStrategy (Context Expr)
applicativeOrderStrategy =
  label "Applicative order reduction"
  $ innermost $ liftToContext βRule

normalForms :: [(String, String, Expr -> Bool)]
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
  , equivalence   = withoutContext αβEquiv
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
