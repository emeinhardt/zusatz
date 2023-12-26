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

-- import Data.Fix qualified as FX
import Data.Fix
  ( Fix (Fix
        -- , unFix
        )
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

-- | A free Boolean algebra.
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
  deriving stock (Eq, Ord, Show, Generic, Functor, Generic1)

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
  project (Not     b    ) = NotF b
  project (Lit     b    ) = LitF b
  project (Ands    bs   ) = AndsF  bs
  project (Ors     bs   ) = OrsF   bs
  project (Nands   bs   ) = NandsF bs
  project (Nors    bs   ) = NorsF  bs
  project (Id      lab b) = IdF    lab b

instance Corecursive Formula where
  embed (AndF     p q  ) = And     p q
  embed (OrF      p q  ) = Or      p q
  embed (XorF     p q  ) = Xor     p q
  embed (ImpliesF p q  ) = Implies p q
  embed (IffF     p q  ) = Iff     p q
  embed (IteF     f t b) = Ite f t b
  embed (NotF     b    ) = Not b
  embed (LitF     b    ) = Lit b
  embed (AndsF    bs   ) = Ands  bs
  embed (OrsF     bs   ) = Ors   bs
  embed (NandsF   bs   ) = Nands bs
  embed (NorsF    bs   ) = Nors  bs
  embed (IdF      lab b) = Id    lab b

-- | Algebra for folding any 'FormulaF' formula into a 'Boolean' instance.
fromFormulaAlg ∷ ∀ b. (Boolean b) ⇒ FormulaF b → b
fromFormulaAlg (AndF     p q  ) =  p  &&   q
fromFormulaAlg (OrF      p q  ) =  p  ||   q
fromFormulaAlg (XorF     p q  ) =  p `xor` q
fromFormulaAlg (ImpliesF p q  ) =  p  ==>  q
fromFormulaAlg (IffF     p q  ) = (p  ==>  q) && (q ==> p)
fromFormulaAlg (IteF     f t b) = choose f t b
fromFormulaAlg (NotF     b    ) = not  b
fromFormulaAlg (LitF     b    ) = bool b
fromFormulaAlg (AndsF    bs   ) = and  bs
fromFormulaAlg (OrsF     bs   ) = or   bs
fromFormulaAlg (NandsF   bs   ) = nand bs
fromFormulaAlg (NorsF    bs   ) = nor  bs
fromFormulaAlg (IdF    _ b    ) = b

-- | Flip the truth values of all literals in a formula.
neg ∷ Formula → Formula
neg = cata negAlg

-- | An algebra for recursively flipping the values of all literals in the root
-- node of a formula and all of its subtrees.
negAlg ∷ FormulaF Formula → Formula
negAlg (LitF True ) = Lit False
negAlg (LitF False) = Lit True
negAlg w            = embed w


type FFormula = Fix FormulaF

mkFFormula ∷ Formula → FFormula
mkFFormula = ana project

forgetFFormula ∷ FFormula → Formula
forgetFFormula = cata embed
