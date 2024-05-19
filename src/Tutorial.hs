module Tutorial where

import Ideas.Common.Library
import Ideas.Main.Default

-- A copy of the Ideas tutorial, with the Literate commentary stripped out

data Expr
  = Add Expr Expr
  | Negate Expr
  | Con Int
  deriving stock (Eq, Show, Read)

-- expression 5+(-2)
expr1 :: Expr
expr1 = Add (Con 5) (Negate (Con 2))

-- expression (-2)+(3+5)
expr2 :: Expr
expr2 = Add (Negate (Con 2)) (Add (Con 3) (Con 5))

addRule :: Rule Expr
addRule = describe "Add two numbers" $ makeRule "eval.add" f
  where
    f :: Expr -> Maybe Expr
    f (Add (Con x) (Con y)) = Just $ Con (x+y)
    f _ = Nothing

negateRule :: Rule Expr
negateRule = describe "Negate number" $ makeRule "eval.negate" f
  where
    f :: Expr -> Maybe Expr
    f (Negate (Con x)) = Just $ Con (-x)
    f _ = Nothing

addOrNegate :: LabeledStrategy Expr
addOrNegate = label "add-or-negate" $
  addRule .|. negateRule

minimalExercise :: Exercise Expr
minimalExercise = emptyExercise
  { exerciseId    = describe "Evaluate an expression (minimal)" $ newId "eval.minimal"
  , strategy      = liftToContext addOrNegate
  , prettyPrinter = show
  }

addSymbol, negateSymbol :: Symbol
addSymbol    = newSymbol "add"
negateSymbol = newSymbol "negate"

fromTermWith :: IsTerm a => (Symbol -> [a] -> Maybe a) -> Term -> Maybe a
fromTermWith f a = do
  (s, xs) <- getFunction a
  ys      <- mapM fromTerm xs
  f s ys

instance IsTerm Expr where
  toTerm (Add x y)  = binary addSymbol (toTerm x) (toTerm y)
  toTerm (Negate x) = unary negateSymbol (toTerm x)
  toTerm (Con x)    = TNum (toInteger x)

  fromTerm (TNum x) = return (Con (fromInteger x))
  fromTerm term     = fromTermWith f term
    where
      f s [x]    | s == negateSymbol = return (Negate x)
      f s [x, y] | s == addSymbol    = return (Add x y)
      f _ _ = fail "invalid expression"

  termDecoder = error "TODO termDecoder"

evalStrategy :: LabeledStrategy (Context Expr)
evalStrategy = label "eval" $
  repeatS (somewhere (liftToContext addOrNegate))

basicExercise :: Exercise Expr
basicExercise = emptyExercise
  { exerciseId    = describe "Evaluate an expression (basic)" $ newId "eval.basic"
  , strategy      = evalStrategy
  , navigation    = termNavigator
  , prettyPrinter = show
  }

eqExpr :: Expr -> Expr -> Bool
eqExpr x y = eval x == eval y

eval :: Expr -> Int
eval (Add x y)  = eval x + eval y
eval (Negate x) = -eval x
eval (Con x)    = x

isCon :: Expr -> Bool
isCon (Con _) = True
isCon _       = False

evalExercise :: Exercise Expr
evalExercise = emptyExercise
  { exerciseId    = describe "Evaluate an expression (full)" $ newId "eval.full"
  , status        = Experimental
  , strategy      = evalStrategy
  , prettyPrinter = show
  , navigation    = termNavigator
  , parser        = (\case Nothing -> Left "Parse error"; Just a -> a) . readM
  , equivalence   = withoutContext eqExpr
  , similarity    = withoutContext (==)
  , ready         = predicate isCon
  , examples      = examplesFor Easy [expr1, expr2]
  }

dr :: DomainReasoner
dr =
  describe "Domain reasoner for tutorial"
    (newDomainReasoner "eval")
    { exercises = [Some minimalExercise, Some basicExercise, Some evalExercise]
    , services  = myServices
    }

myServices :: [Service]
myServices = metaServiceList dr ++ serviceList

tutorialMain :: IO ()
tutorialMain = defaultMain dr
