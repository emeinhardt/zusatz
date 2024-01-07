-- | This module contains affine traversals for (non-recursively) viewing or
-- updating the values inside a 'Formula' or 'FormulaF' constructor.

module Zusatz.Formula.Optics
  ( _label
  , _lit
  , _else
  , _then
  , _cond
  , _ite

  , _arg
  , _argL
  , _argR
  , _argLR
  , _args

  , _labelF
  , _litF
  , _elseF
  , _thenF
  , _condF
  , _iteF

  , _argF
  , _argLF
  , _argRF
  , _argLRF
  , _argsF
  )
  where

import Prelude

import Data.Sequence
  ( Seq
  )

import Optics
  ( AffineTraversal
  , atraversal
  )

import Zusatz.Formula.Class
  ( Formula ( Lit
            , Id
            , Not
            , And
            , Or
            , Xor
            , Iff
            , Implies
            , Ite
            , Ands
            , Ors
            , Nands
            , Nors
            )
  , FormulaF ( LitF
             , IdF
             , NotF
             , AndF
             , OrF
             , XorF
             , IffF
             , ImpliesF
             , IteF
             , AndsF
             , OrsF
             , NandsF
             , NorsF
             )
  )

-- | View or update the label of a 'Formula'.
_label ∷ AffineTraversal Formula Formula String String
_label =
  let view_   (Id lab _)     = Right lab
      view_   f              = Left  f
      update_ (Id _   f) lab = Id lab f
      update_ f          _   = f
  in  atraversal view_ update_

-- | View or update the label of a 'FormulaF'.
_labelF ∷ AffineTraversal (FormulaF a) (FormulaF a) String String
_labelF =
  let view_   (IdF lab _)     = Right lab
      view_   f               = Left  f
      update_ (IdF _   f) lab = IdF lab f
      update_ f           _   = f
  in  atraversal view_ update_

-- | View or update the 'Bool' inside a 'Lit' term.
_lit ∷ AffineTraversal Formula Formula Bool Bool
_lit =
  let view_   (Lit b)   = Right b
      view_   f         = Left  f
      update_ (Lit _) b = Lit b
      update_ f       _ = f
  in  atraversal view_ update_

-- | View or update the 'Bool' inside a 'LitF' term.
_litF ∷ AffineTraversal (FormulaF a) (FormulaF a) Bool Bool
_litF =
  let view_   (LitF b)   = Right b
      view_   f          = Left  f
      update_ (LitF _) b = LitF b
      update_ f        _ = f
  in  atraversal view_ update_

-- | View or update the else branch of an 'Ite' term.
_else ∷ AffineTraversal Formula Formula Formula Formula
_else =
  let view_   (Ite f _ _)   = Right f
      view_   f             = Left  f
      update_ (Ite _ t c) f = Ite f t c
      update_ f           _ = f
  in atraversal view_ update_

-- | View or update the else branch of an 'IteF' term.
_elseF ∷ AffineTraversal (FormulaF a) (FormulaF a) a a
_elseF =
  let view_   (IteF f _ _)   = Right f
      view_   f              = Left  f
      update_ (IteF _ t c) f = IteF f t c
      update_ f            _ = f
  in atraversal view_ update_

-- | View or update the then branch of an 'Ite' term.
_then ∷ AffineTraversal Formula Formula Formula Formula
_then =
  let view_   (Ite _ f _)   = Right f
      view_   f             = Left  f
      update_ (Ite f _ c) t = Ite f t c
      update_ f           _ = f
  in atraversal view_ update_

-- | View or update the then branch of an 'IteF' term.
_thenF ∷ AffineTraversal (FormulaF a) (FormulaF a) a a
_thenF =
  let view_   (IteF _ f _)   = Right f
      view_   f              = Left  f
      update_ (IteF f _ c) t = IteF f t c
      update_ f            _ = f
  in atraversal view_ update_

-- | View or update the condition of an 'Ite' term.
_cond ∷ AffineTraversal Formula Formula Formula Formula
_cond =
  let view_   (Ite _ _ c)   = Right c
      view_   f             = Left  f
      update_ (Ite f t _) c = Ite f t c
      update_ f           _ = f
  in atraversal view_ update_

-- | View or update the condition of an 'IteF' term.
_condF ∷ AffineTraversal (FormulaF a) (FormulaF a) a a
_condF =
  let view_   (IteF _ _ c)   = Right c
      view_   f              = Left  f
      update_ (IteF f t _) c = IteF f t c
      update_ f            _ = f
  in atraversal view_ update_


-- | View or update all components of an 'Ite' term.
_ite ∷ AffineTraversal Formula Formula (Formula, Formula, Formula) (Formula, Formula, Formula)
_ite =
  let view_   (Ite f t c)           = Right (f, t, c)
      view_   f                     = Left  f
      update_ (Ite {}   ) (f, t, c) = Ite f t c
      update_ f           _         = f
  in atraversal view_ update_

-- | View or update all components of an 'IteF' term.
_iteF ∷ AffineTraversal (FormulaF a) (FormulaF a) (a, a, a) (a, a, a)
_iteF =
  let view_   (IteF f t c)           = Right (f, t, c)
      view_   f                      = Left  f
      update_ (IteF {}   ) (f, t, c) = IteF f t c
      update_ f           _          = f
  in atraversal view_ update_



-- | View or update the unique formula contained inside a 'Formula' term,
-- assuming it has such a unique formula.
_arg ∷ AffineTraversal Formula Formula Formula Formula
_arg =
  let view_   (Not     f)   = Right f
      view_   (Id    _ f)   = Right f
      view_   f             = Left  f
      update_ (Not     _) f = Not    f
      update_ (Id  lab _) f = Id lab f
      update_ f           _ = f
  in  atraversal view_ update_

-- | View or update the unique formula contained inside a 'FormulaF' term,
-- assuming it has such a unique formula.
_argF ∷ AffineTraversal (FormulaF a) (FormulaF a) a a
_argF =
  let view_   (NotF     f)   = Right f
      view_   (IdF    _ f)   = Right f
      view_   f              = Left  f
      update_ (NotF     _) f = NotF    f
      update_ (IdF  lab _) f = IdF lab f
      update_ f            _ = f
  in  atraversal view_ update_

-- | View or update the left formula contained inside a 'Formula' term
-- containing exactly two formulas.
_argL ∷ AffineTraversal Formula Formula Formula Formula
_argL =
  let view_   (And     f _)   = Right f
      view_   (Or      f _)   = Right f
      view_   (Xor     f _)   = Right f
      view_   (Iff     f _)   = Right f
      view_   (Implies f _)   = Right f
      view_   f               = Left  f
      update_ (And     _ r) f = And     f r
      update_ (Or      _ r) f = Or      f r
      update_ (Xor     _ r) f = Xor     f r
      update_ (Iff     _ r) f = Iff     f r
      update_ (Implies _ r) f = Implies f r
      update_ f             _ = f
  in  atraversal view_ update_


-- | View or update the left formula contained inside a 'FormulaF' term
-- containing exactly two formulas.
_argLF ∷ AffineTraversal (FormulaF a) (FormulaF a) a a
_argLF =
  let view_   (AndF     f _)   = Right f
      view_   (OrF      f _)   = Right f
      view_   (XorF     f _)   = Right f
      view_   (IffF     f _)   = Right f
      view_   (ImpliesF f _)   = Right f
      view_   f                = Left  f
      update_ (AndF     _ r) f = AndF     f r
      update_ (OrF      _ r) f = OrF      f r
      update_ (XorF     _ r) f = XorF     f r
      update_ (IffF     _ r) f = IffF     f r
      update_ (ImpliesF _ r) f = ImpliesF f r
      update_ f              _ = f
  in  atraversal view_ update_

-- | View or update the right formula contained inside a 'Formula' term
-- containing exactly two formulas.
_argR ∷ AffineTraversal Formula Formula Formula Formula
_argR =
  let view_   (And     _ f)   = Right f
      view_   (Or      _ f)   = Right f
      view_   (Xor     _ f)   = Right f
      view_   (Iff     _ f)   = Right f
      view_   (Implies _ f)   = Right f
      view_   f               = Left  f
      update_ (And     l _) f = And     l f
      update_ (Or      l _) f = Or      l f
      update_ (Xor     l _) f = Xor     l f
      update_ (Iff     l _) f = Iff     l f
      update_ (Implies l _) f = Implies l f
      update_ f             _ = f
  in  atraversal view_ update_


-- | View or update the right formula contained inside a 'FormulaF' term
-- containing exactly two formulas.
_argRF ∷ AffineTraversal (FormulaF a) (FormulaF a) a a
_argRF =
  let view_   (AndF     _ f)   = Right f
      view_   (OrF      _ f)   = Right f
      view_   (XorF     _ f)   = Right f
      view_   (IffF     _ f)   = Right f
      view_   (ImpliesF _ f)   = Right f
      view_   f                = Left  f
      update_ (AndF     l _) f = AndF     l f
      update_ (OrF      l _) f = OrF      l f
      update_ (XorF     l _) f = XorF     l f
      update_ (IffF     l _) f = IffF     l f
      update_ (ImpliesF l _) f = ImpliesF l f
      update_ f              _ = f
  in  atraversal view_ update_


-- | View or update both formulas contained inside a 'Formula' term
-- containing exactly two formulas.
_argLR ∷ AffineTraversal Formula Formula (Formula, Formula) (Formula, Formula)
_argLR =
  let view_   (And     l r)        = Right (l, r)
      view_   (Or      l r)        = Right (l, r)
      view_   (Xor     l r)        = Right (l, r)
      view_   (Iff     l r)        = Right (l, r)
      view_   (Implies l r)        = Right (l, r)
      view_   f                    = Left  f
      update_ (And     _ _) (l, r) = And     l r
      update_ (Or      _ _) (l, r) = Or      l r
      update_ (Xor     _ _) (l, r) = Xor     l r
      update_ (Iff     _ _) (l, r) = Iff     l r
      update_ (Implies _ _) (l, r) = Implies l r
      update_ f             _      = f
  in  atraversal view_ update_


-- | View or update both formulas contained inside a 'FormulaF' term
-- containing exactly two formulas.
_argLRF ∷ AffineTraversal (FormulaF a) (FormulaF a) (a, a) (a, a)
_argLRF =
  let view_   (AndF     l r)        = Right (l, r)
      view_   (OrF      l r)        = Right (l, r)
      view_   (XorF     l r)        = Right (l, r)
      view_   (IffF     l r)        = Right (l, r)
      view_   (ImpliesF l r)        = Right (l, r)
      view_   f                     = Left  f
      update_ (AndF     _ _) (l, r) = AndF     l r
      update_ (OrF      _ _) (l, r) = OrF      l r
      update_ (XorF     _ _) (l, r) = XorF     l r
      update_ (IffF     _ _) (l, r) = IffF     l r
      update_ (ImpliesF _ _) (l, r) = ImpliesF l r
      update_ f             _       = f
  in  atraversal view_ update_


-- | View or update the collection of formulas contained inside a 'Formula' 
-- term, assuming it has such a collection.
_args ∷ AffineTraversal Formula Formula (Seq Formula) (Seq Formula)
_args =
  let view_   (Ands  fs)    = Right fs
      view_   (Ors   fs)    = Right fs
      view_   (Nands fs)    = Right fs
      view_   (Nors  fs)    = Right fs
      view_   f             = Left  f
      update_ (Ands   _) fs = Ands  fs
      update_ (Ors    _) fs = Ors   fs
      update_ (Nands  _) fs = Nands fs
      update_ (Nors   _) fs = Nors  fs
      update_ f          _  = f
  in  atraversal view_ update_


-- | View or update the collection of formulas contained inside a 'FormulaF' 
-- term, assuming it has such a collection.
_argsF ∷ AffineTraversal (FormulaF a) (FormulaF a) (Seq a) (Seq a)
_argsF =
  let view_   (AndsF  fs)    = Right fs
      view_   (OrsF   fs)    = Right fs
      view_   (NandsF fs)    = Right fs
      view_   (NorsF  fs)    = Right fs
      view_   f              = Left  f
      update_ (AndsF   _) fs = AndsF  fs
      update_ (OrsF    _) fs = OrsF   fs
      update_ (NandsF  _) fs = NandsF fs
      update_ (NorsF   _) fs = NorsF  fs
      update_ f           _  = f
  in  atraversal view_ update_


