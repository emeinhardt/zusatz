# `zusatz`

`zusatz` is a (WIP) tooling library designed to support working with SAT solvers. In particular it is motivated as a companion to [ersatz](https://hackage.haskell.org/package/ersatz). 

The motivating use case is debugging: given a formula that a solver has found a model for, *why* is the formula true under the model? 

The main module offers functions for annotating and filtering a propositional formula AST that hide information irrelevant to the truth value of the topmost node in the tree. The formula AST also permits textual labelling of nodes to make it easier to quickly find relevant subformulas. 

## Basic Example
In the formula `ex` below, the entire outer `leftBranch` is irrelevant to the truth value of `ex`, and the left half of the outer `rightBranch` is similarly irrelevant:

```haskell
>> leftBranch = (true && true) ∷ Formula
>> rightBranch = (true && false) ∷ Formula
>> ex = leftBranch && rightBranch
>> pPrint ex
And
  ( And ( Lit True ) ( Lit True  ) )
  ( And ( Lit True ) ( Lit False ) )
>> :t withEval
withEval :: Formula -> Cofree FormulaF Bool
>> :t why
why :: Cofree FormulaF Bool -> Cofree FormulaF (Maybe Bool)
>> pPrint $ why . withEval $ ex
Just False :< AndF
    ( Nothing    :< AndF ( Nothing :< LitF True ) ( Nothing    :< LitF True  ) )
    ( Just False :< AndF ( Nothing :< LitF True ) ( Just False :< LitF False ) )
>> pPrint $ quiet . why . withEval $ ex
Just False :< MaybeT
  ( AndF Nothing
         ( Just ( Just False :< MaybeT
                  ( AndF Nothing
                    ( Just ( Just False :< MaybeT ( LitF False ) ) ) ) ) ) )
```

## Gory details

The two main datatypes are `Formula` and a base functor `FormulaF`. As you can see from the example above, annotations are currently handled via the `Cofree` comonad over `FormulaF`, but this may change.

## Status

The package is a WIP that needs more use/evaluation. Comments are welcome.
