# lc-reasoner

Domain reasoner for the λ-calculus, implemented using the [Ideas](https://ideas.science.uu.nl/) library.

## Description of the reasoner

This project implements a domain reasoner for the λ-calculus using the Ideas library. It supports exercises
for reducing λ-terms step-by-step to various normal forms (β-normal form, head normal form, and weak-head normal
form), using either normal-order or applicative-order evaluation.

The reasoner uses a named, first-order representation for λ-terms, and uses the 'IsTerm' class to serialize and
deserialize the AST into the library's 'Term's.

The reasoner defines 2 rewrite rules for reducing expressions, and a third buggy rule that is commonly applied by students:

* The β-rule, which applies a single β-reduction of the form `(λx. M) N => M[N/x]`, but only if the substitution captures
no variables (in other words, if no α-renaming is necessary).
* The α-rule, which performs α-renaming on a single λ-abstraction subterm, replacing the name bound by the λ with a fresh one, in order to unblock a subsequent application of the β-rule.
* The buggy β-rule, which applies a single β-reduction without checking whether variables are captured during substitution, thus potentially changing the expression's meaning.

These rules are then combined into 2 different strategies, each corresponding to an evaluation order:

* The normal-order strategy, which keeps applying the β-rule, and if it fails, then the α-rule (using the `|>` combinator), to the leftmost outermost subterm (using the `outermost` combinator).
* The applicative-order strategy, which applies the same rules, but to the leftmost _innermost_ subterm instead.

Using these rules and strategies, the domain reasoner exposes 6 exercises, one for each combination of normal form
and reduction order. Each exercise uses a different `ready` predicate to check for the appropiate normal form. The α-equivalence relation is used to check for the `similarity` of terms, and αβ-equivalence is used when checking for `equivalence`. All these operations take care to not enter an infinite loop when reducing terms with no normal form (e.g. `(λx. x x) (λx. x x)`).

This domain reasoner could be of great utility to students learning about the Lambda Calculus, as it can help them learn
the term reduction process (which usually feels daunting due to the number of steps required) in a gradual fashion,
starting with simple examples, and increasing the difficulty along the way. The ability to provide feedback at each step, and to recognize buggy answers, is especially helpful, as it prevents students from getting stuck in dead-end solutions.

Furthermore, the inclusion of exercises for multiple reduction orders and normal forms allows students to
understand their differences and similarities, helping them learn their applicability in different contexts.

## Build instructions

The project has been tested with the following toolchain versions:

* GHC 9.2.8
* cabal-install 3.10.3.0

To build, run the following command:

```sh
cabal build
```

To run the project, giving it inputs from a local XML file, use:

```sh
cabal run . -- -f <FILE>
```

To run the project as a CGI script, first build it, then copy the resulting executable to your cgi-bin directory (locations depend on your Cabal version and HTTP server, see [build.sh](build.sh)).
