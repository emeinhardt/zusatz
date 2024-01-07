{-# OPTIONS_HADDOCK show-extensions #-}
-- |

module Zusatz.Formula.Class
  ( Formula ( Id
            , Lit
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
  , Conj (Conj, unConj)
  , Disj (Disj, unDisj)
  , fromFormula
  , neg
  , isLabeled

  , FormulaF ( IdF
             , LitF
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
  , fromFormulaAlg
  , negAlg
  , isLabeledF

  , FFormula
  , mkFFormula
  , forgetFFormula
  ) where

import Prelude hiding
  ( not
  , or
  , and
  , (&&)
  , (||)
  , any
  , all
  )
import Prelude.Unicode
  ( (∘)
  )

import GHC.Generics
  ( Generic
  , Generic1
  )
import Data.Functor.Classes
  ( Eq1
  , liftEq
  , Ord1
  , liftCompare
  , Read1
  , liftReadsPrec
  , Show1
  , liftShowsPrec
  )
import Data.Functor.Classes.Generic
  ( liftEqDefault
  , liftCompareDefault
  , liftReadsPrecDefault
  , liftShowsPrecDefault
  )

import Data.Fix
  ( Fix 
  )

import qualified Data.Foldable as F
import Data.Foldable
  ( toList
  )
import qualified Data.Sequence as Seq
import Data.Sequence
  ( Seq
  )

import Data.Functor.Foldable
  ( Base
  , Recursive
  , project
  , Corecursive
  , embed
  , cata
  , ana
  )

import Ersatz.Bit
  ( Boolean
  , bool
  , true
  , false
  , (&&)
  , (||)
  , (==>)
  , not
  , xor
  , choose
  , and
  , or
  , nand
  , nor
  , all
  , any
  )

-- | Optionally identifier-labeled propositional formulas. This fragment of 
-- @ersatz@'s 'Boolean' interface only includes inspectable representations: it
-- intentionally /excludes/ any constructors that would wrap a function — 
-- 'all', 'any', or (novel relative to 'Boolean') anything like a predicate.
--
-- A salient extension or alternative to this might be a 'Category' or 
-- 'Semiarrow'-like type that can represent Boolean circuits.
data Formula =
    Id      !String !Formula
  | Lit     !Bool
  | And     !Formula !Formula
  | Or      !Formula !Formula
  | Implies !Formula !Formula
  | Not     !Formula
  | Xor     !Formula !Formula
  | Ite     !Formula !Formula !Formula
  | Iff     !Formula !Formula
  | Ands    !(Seq Formula)
  | Ors     !(Seq Formula)
  | Nands   !(Seq Formula)
  | Nors    !(Seq Formula)
  deriving stock (Eq, Ord, Show, Generic)

-- | A newtype for a 'Formula' 'Monoid' using 'And'.
newtype Conj a = Conj { unConj ∷ a }
  deriving stock (Eq, Ord, Show, Generic, Functor, Generic1)

instance Semigroup (Conj Formula) where
  (Conj p) <> (Conj q) = Conj (And p q)

instance Monoid (Conj Formula) where
  mempty = Conj ∘ Lit $ True

-- | A newtype for a 'Formula' 'Monoid' using 'Or'.
newtype Disj a = Disj { unDisj ∷ a }
  deriving stock (Eq, Ord, Show, Generic, Functor, Generic1)

instance Semigroup (Disj Formula) where
  (Disj p) <> (Disj q) = Disj (Or p q)

instance Monoid (Disj Formula) where
  mempty = Disj ∘ Lit $ False

instance Boolean Formula where
  bool   = Lit
  true   = bool True
  false  = bool False
  (&&)   = And
  (||)   = Or
  (==>)  = Implies
  not    = Not
  xor    = Xor
  choose = Ite
  and    = Ands  ∘ Seq.fromList ∘ toList
  or     = Ors   ∘ Seq.fromList ∘ toList
  nand   = Nands ∘ Seq.fromList ∘ toList
  nor    = Nors  ∘ Seq.fromList ∘ toList
  all f  = unConj ∘ F.foldMap (Conj ∘ f)
  any f  = unDisj ∘ F.foldMap (Disj ∘ f)


-- | Fold any 'FormulaF' formula into a 'Boolean' instance.
fromFormula ∷ (Boolean b) ⇒ Formula → b
fromFormula = cata fromFormulaAlg

-- | Predicate indicating whether the 'Formula' term is labeled with an
-- identifier.
isLabeled ∷ Formula → Bool
isLabeled (Id _ _) = True
isLabeled _        = False


-- | The base functor for 'Formula'.
data FormulaF a =
    IdF      !String !a
  | LitF     !Bool
  | AndF     !a !a
  | OrF      !a !a
  | ImpliesF !a !a
  | NotF     !a
  | XorF     !a !a
  | IteF     !a !a !a
  | IffF     !a !a
  | AndsF    !(Seq a)
  | OrsF     !(Seq a)
  | NandsF   !(Seq a)
  | NorsF    !(Seq a)
  deriving stock (Eq, Ord, Show, Generic, Generic1)
  deriving stock (Functor, Foldable, Traversable)

instance Eq1 FormulaF where
  liftEq = liftEqDefault

instance Ord1 FormulaF where
  liftCompare = liftCompareDefault

instance Read1 FormulaF where
  liftReadsPrec = liftReadsPrecDefault

instance Show1 FormulaF where
  liftShowsPrec = liftShowsPrecDefault

type instance Base Formula = FormulaF


instance Recursive Formula where
  project (And     p q  ) = AndF     p q
  project (Or      p q  ) = OrF      p q
  project (Xor     p q  ) = XorF     p q
  project (Implies p q  ) = ImpliesF p q
  project (Iff     p q  ) = IffF     p q
  project (Ite     f t b) = IteF f t b
  project (Not     f    ) = NotF f
  project (Lit     b    ) = LitF b
  project (Ands    fs   ) = AndsF  fs
  project (Ors     fs   ) = OrsF   fs
  project (Nands   fs   ) = NandsF fs
  project (Nors    fs   ) = NorsF  fs
  project (Id      lab f) = IdF    lab f

instance Corecursive Formula where
  embed (AndF     p q  ) = And     p q
  embed (OrF      p q  ) = Or      p q
  embed (XorF     p q  ) = Xor     p q
  embed (ImpliesF p q  ) = Implies p q
  embed (IffF     p q  ) = Iff     p q
  embed (IteF     f t b) = Ite f t b
  embed (NotF     f    ) = Not f
  embed (LitF     b    ) = Lit b
  embed (AndsF    fs   ) = Ands  fs
  embed (OrsF     fs   ) = Ors   fs
  embed (NandsF   fs   ) = Nands fs
  embed (NorsF    fs   ) = Nors  fs
  embed (IdF      lab f) = Id    lab f

-- | Algebra for folding any 'FormulaF' formula into a 'Boolean' instance.
fromFormulaAlg ∷ ∀ b. (Boolean b) ⇒ FormulaF b → b
fromFormulaAlg (AndF     p q  ) =  p  &&   q
fromFormulaAlg (OrF      p q  ) =  p  ||   q
fromFormulaAlg (XorF     p q  ) =  p `xor` q
fromFormulaAlg (ImpliesF p q  ) =  p  ==>  q
fromFormulaAlg (IffF     p q  ) = (p  ==>  q) && (q ==> p)
fromFormulaAlg (IteF     f t b) = choose f t b
fromFormulaAlg (NotF     f    ) = not  f
fromFormulaAlg (LitF     b    ) = bool b
fromFormulaAlg (AndsF    fs   ) = and  fs
fromFormulaAlg (OrsF     fs   ) = or   fs
fromFormulaAlg (NandsF   fs   ) = nand fs
fromFormulaAlg (NorsF    fs   ) = nor  fs
fromFormulaAlg (IdF    _ f    ) = f

-- | Flip the truth values of all literals in a formula.
neg ∷ Formula → Formula
neg = cata negAlg

-- | An algebra for recursively flipping the values of all literals in the root
-- node of a formula and all of its subtrees.
negAlg ∷ FormulaF Formula → Formula
negAlg (LitF True ) = Lit False
negAlg (LitF False) = Lit True
negAlg w            = embed w

-- | Predicate indicating whether the 'FormulaF' term is labeled with an
-- identifier.
isLabeledF ∷ FormulaF a → Bool
isLabeledF (IdF _ _) = True
isLabeledF _         = False


type FFormula = Fix FormulaF

mkFFormula ∷ Formula → FFormula
mkFFormula = ana project

forgetFFormula ∷ FFormula → Formula
forgetFFormula = cata embed
