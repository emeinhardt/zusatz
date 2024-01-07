# `zusatz`

`zusatz` is a (WIP) tooling library designed to support working with SAT solvers. In particular it is motivated as a companion to [ersatz](https://hackage.haskell.org/package/ersatz). 

The motivating use case is debugging: given a formula that a solver has found a model for, *why* is the formula true under the model? The formula type supports adding an identifier to any `Formula` (sub)term and the `Zusatz.Formula.Cofree` module includes functions for annotating and filtering a propositional formula AST that hide information irrelevant to the truth value of the topmost node in the term (see examples below); that module also includes functions for identifying subterms of one formula that match the 'shape' of another (see exmaples below).

## The `Formula` type

```haskell
data Formula =
    Id      String Formula
  | Lit     Bool
  | And     Formula Formula
  | Or      Formula Formula
  | Implies Formula Formula
  | Not     Formula
  | Xor     Formula Formula
  | Ite     Formula Formula Formula
  | Iff     Formula Formula
  | Ands    (Seq Formula)
  | Ors     (Seq Formula)
  | Nands   (Seq Formula)
  | Nors    (Seq Formula)
```

## Basic Example - why is a formula true?
In the formula `ex` below, the entire outer `leftBranch` is irrelevant to the truth value of `ex`, and the left half of the outer `rightBranch` is similarly irrelevant:

```haskell
>>> leftBranch = (true && true) ∷ Formula
>>> rightBranch = (true && false) ∷ Formula
>>> ex = leftBranch && rightBranch
>>> pPrint ex
And
  ( And ( Lit True ) ( Lit True  ) )
  ( And ( Lit True ) ( Lit False ) )
>>> :t withEval
withEval :: Formula -> Cofree FormulaF Bool
>>> :t why
why :: Cofree FormulaF Bool -> Cofree FormulaF (Maybe Bool)
>>> pPrint $ why . withEval $ ex
Just False :< AndF
    ( Nothing    :< AndF ( Nothing :< LitF True ) ( Nothing    :< LitF True  ) )
    ( Just False :< AndF ( Nothing :< LitF True ) ( Just False :< LitF False ) )
>>> pPrint $ quiet . why . withEval $ ex
Just False :< MaybeT
  ( AndF Nothing
         ( Just ( Just False :< MaybeT
                  ( AndF Nothing
                    ( Just ( Just False :< MaybeT ( LitF False ) ) ) ) ) ) )
```

## Matching subterms

```haskell
>>> mkImplies p q = Or (Not p) q
>>> impliesEx = mkImplies (Lit True) (Lit False)
>>> oneMatch = Not impliesEx
>>> subtreeMatch impliesEx oneMatch
      False :< NotF (True :< OrF (False :< NotF (False :< LitF True)) (False :< LitF False))
>>> multipleMatches = mkImplies impliesEx oneMatch
>>> pPrint $ subtreeMatch impliesEx multipleMatches
      True :< OrF
        ( False :< NotF
          ( True :< OrF
            ( False :< NotF ( False :< LitF True ) ) ( False :< LitF False ) ) )
        ( False :< NotF
          ( True :< OrF
            ( False :< NotF ( False :< LitF True ) ) ( False :< LitF False ) ) )
>>> multipleMatches' = Id "foo" $ mkImplies (Id "bar" impliesEx) oneMatch
>>> pPrint $ subtreeMatch impliesEx multipleMatches'
      True :< IdF "foo"  -- Note that the annotation of an 'IdF' matches its child's.
        ( True :< OrF
          ( False :< NotF
            ( True :< IdF "bar"
              ( True :< OrF
                ( False :< NotF ( False :< LitF True ) ) ( False :< LitF False ) ) ) )
          ( False :< NotF
            ( True :< OrF
              ( False :< NotF ( False :< LitF True ) ) ( False :< LitF False ) ) ) )
```

## Gory details

The two main datatypes are `Formula` and a base functor `FormulaF`. As you can see from the example above, annotations are currently handled via the `Cofree` comonad over `FormulaF`, but this may change.

## Status

The package is a WIP that needs more use/evaluation. Comments are welcome.
