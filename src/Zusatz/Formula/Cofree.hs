{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
-- | This module contains functions that uses 'Cofree' to annotate
-- 'Formula'/'FormulaF' values.

module Zusatz.Formula.Cofree
  ( bimapCF
  , forgetCF
  , forgetCFFix

  , erase

  -- * Evaluation-derived annotations
  , withEval
  , why
  , quiet
  , quietUnsafe
  , whyRCoalg
  , quietRCoalg
  , quietRCoalgUnsafe
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
import Control.Arrow
  ( (&&&)
  )
import qualified Data.Bool as B
import Data.Maybe
  ( isJust
  , fromJust
  )


import Data.Fix
  ( Fix (Fix)
  )

import Data.Functor.Foldable
  ( project
  , cata
  , apo
  )

import Control.Comonad
  ( extract
  )
import qualified Control.Comonad.Trans.Cofree as CFT
import Control.Comonad.Trans.Cofree
  ( CofreeF
  )
import qualified Control.Comonad.Cofree as CF
import Control.Comonad.Cofree
  ( Cofree ((:<))
  )
import Control.Monad.Trans.Maybe
  ( MaybeT ( MaybeT
           -- , runMaybeT
           )
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

import Zusatz.Formula.Class
  ( Formula
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
  , forgetFFormula
  )


-- -- TODO dev block
-- import Text.Pretty.Simple qualified as S
-- import Text.Pretty.Simple
--   ( pPrint
--   , pPrintOpt
--   , defaultOutputOptionsDarkBg
--   , defaultColorOptionsDarkBg
--   , OutputOptions( outputOptionsIndentAmount
--                  , outputOptionsPageWidth
--                  , outputOptionsCompact
--                  , outputOptionsCompactParens
--                  , outputOptionsInitialIndent
--                  , outputOptionsColorOptions
--                  , outputOptionsStringStyle
--                  )
--   , CheckColorTty(CheckColorTty, NoCheckColorTty)
--   )


-- myOpts = defaultOutputOptionsDarkBg { outputOptionsIndentAmount  = 2
--                                     , outputOptionsPageWidth     = 110
--                                     , outputOptionsCompact       = False
--                                     , outputOptionsCompactParens = True
--                                     }
-- -- pPrint' = pPrintOpt CheckColorTty myOpts


justWhen ∷ ∀ a. (a → Bool) → a → Maybe a
justWhen = ((B.bool Nothing ∘ Just) <*>)

eitherWhen ∷ ∀ a b c. (a → Bool) → (a → b) → (a → c) → a → Either b c
eitherWhen p l r a = B.bool (Left ∘ l $ a) (Right ∘ r $ a) (p a)

(<&) ∷ ∀ f a b. a → f b → CofreeF f a b
(<&) = (CFT.:<)



-- | Analogue of @bimap@ from @Data.Bifunctor@ for @Cofree@ values: the first
-- function transforms an existing annotation and the second transforms the
-- annotated value.
--
-- Note that the functor instance for 'Cofree' already lets you transform the
-- annotation if that is all you want.
bimapCF ∷ ∀ f g a b c.
           (a → b)
        → (f (Cofree f a) → g c)
        → Cofree f a
        → CofreeF g b c
bimapCF f g (h :< t) = f h <& g t


-- | Forget all annotations.
forgetCF ∷ Cofree FormulaF a → Formula
forgetCF = forgetFFormula . forgetCFFix

-- | More general variant of 'forgetCF' useful when e.g. you have transformed
-- `FormulaF`, composed it with another 'Functor', etc.
forgetCFFix ∷ Functor f ⇒ Cofree f a → Fix f
forgetCFFix = cata (\(_ CFT.:< z) → Fix z)





-- | Erase an optional annotation on a formula and all its subformulas.
erase ∷ ∀ a. Cofree FormulaF a → Cofree FormulaF (Maybe a)
erase = fmap (const Nothing)



-- | Annotate each node of a formula with the evaluation of its subtree.
withEval ∷ Formula → Cofree FormulaF Bool
withEval = CF.unfold (cata fromFormulaAlg &&& project)



-- | Transform a formula where each node is annotated with its evaluation to one
-- where nodes whose truth value is unconditionally irrelevant to determining
-- the truth value of their parents have their annotation stripped.
--
-- == Example
--
-- >> leftBranch = (true && true) :: Formula
-- >> rightBranch = (true && false) :: Formula
-- >> ex = leftBranch && rightBranch
-- >> pPrint ex
-- > And
-- >   ( And ( Lit True ) ( Lit True  ) )
-- >   ( And ( Lit True ) ( Lit False ) )
-- >> pPrint $ why . withEval $ ex
-- > Just False :< AndF
-- >     ( Nothing    :< AndF ( Nothing :< LitF True ) ( Nothing    :< LitF True  ) )
-- >     ( Just False :< AndF ( Nothing :< LitF True ) ( Just False :< LitF False ) )
why ∷ Cofree FormulaF Bool → Cofree FormulaF (Maybe Bool)
why = apo whyRCoalg

whyRCoalg ∷
    Cofree FormulaF Bool
  → CofreeF FormulaF (Maybe Bool) (Either (Cofree FormulaF (Maybe Bool))
                                          (Cofree FormulaF Bool       ))
whyRCoalg t@(False :< AndsF  _) = bimapCF Just (fmap (eitherWhen (not ∘ extract) erase id)) t
whyRCoalg t@(True  :< OrsF   _) = bimapCF Just (fmap (eitherWhen        extract  erase id)) t
whyRCoalg t@(True  :< NandsF _) = bimapCF Just (fmap (eitherWhen (not ∘ extract) erase id)) t
whyRCoalg t@(False :< NorsF  _) = bimapCF Just (fmap (eitherWhen        extract  erase id)) t
whyRCoalg (True :< IteF f t b) = case (f,t,b) of
  (_        , True :< _, True  :< _) → Just True <& IteF (Left $ erase f) (Right t) (Right b)
  (True :< _, _        , False :< _) → Just True <& IteF (Right f) (Left $ erase t) (Right b)
whyRCoalg (False :< IteF f t b) = case (f,t,b) of
  (_         , False :< _, True  :< _) → Just False <& IteF (Left $ erase f) (Right t) (Right b)
  (False :< _, _         , False :< _) → Just False <& IteF (Right f) (Left $ erase t) (Right b)
whyRCoalg t@(True :< (ImpliesF p q)) = case (p,q) of
  (False :< _, True :< _) → bimapCF Just (fmap Right) t
  (False :< _, _        ) → Just True <& ImpliesF (Right p) (Left $ erase q)
  (_         , True :< _) → Just True <& ImpliesF (Left $ erase p) (Right q)
whyRCoalg t@(False :< (AndF p q)) = case (p,q) of
  (False :< _, False :< _) → bimapCF Just (fmap Right) t
  (False :< _, _         ) → Just False <& AndF (Right p) (Left $ erase q)
  (_         , False :< _) → Just False <& AndF (Left $ erase p) (Right q)
whyRCoalg t@(True :< (OrF p q)) = case (p,q) of
  (True :< _, True :< _) → bimapCF Just (fmap Right) t
  (True :< _, _        ) → Just True <& OrF (Right p) (Left $ erase q)
  (_        , True :< _) → Just True <& OrF (Left $ erase p) (Right q)
whyRCoalg t@(True  :< AndsF  _) = bimapCF Just (fmap Right) t
whyRCoalg t@(False :< OrsF   _) = bimapCF Just (fmap Right) t
whyRCoalg t@(False :< NandsF _) = bimapCF Just (fmap Right) t
whyRCoalg t@(True  :< NorsF  _) = bimapCF Just (fmap Right) t
whyRCoalg t@(True  :< (AndF     _ _)) = bimapCF Just (fmap Right) t
whyRCoalg t@(False :< (OrF      _ _)) = bimapCF Just (fmap Right) t
whyRCoalg t@(False :< (ImpliesF _ _)) = bimapCF Just (fmap Right) t
whyRCoalg t@(_     :< (XorF     _ _)) = bimapCF Just (fmap Right) t
whyRCoalg t@(_     :< (IffF     _ _)) = bimapCF Just (fmap Right) t
whyRCoalg t@(_ :< (NotF _)) = bimapCF Just (fmap Right) t
whyRCoalg t@(_ :< (LitF _)) = bimapCF Just (fmap Right) t
whyRCoalg   (b :< (IdF l w)) = case whyRCoalg w of
  (Just _  CFT.:< _) -> Just b  <& IdF l (Right w)
  (Nothing CFT.:< _) -> Nothing <& IdF l (Left $ erase w)


-- | Given a formula where only nodes whose truth value is relevant to the truth
-- value of their parent have an annotation indicating their truth value, replace
-- every irrelevant subtree with a 'Nothing' placeholder.
--
-- == Example
--
-- >> leftBranch = (true && true) :: Formula
-- >> rightBranch = (true && false) :: Formula
-- >> ex = leftBranch && rightBranch
-- >> pPrint ex
-- > And
-- >   ( And ( Lit True ) ( Lit True  ) )
-- >   ( And ( Lit True ) ( Lit False ) )
-- >> pPrint $ why . withEval $ ex
-- > Just False :< AndF
-- >     ( Nothing    :< AndF ( Nothing :< LitF True ) ( Nothing    :< LitF True  ) )
-- >     ( Just False :< AndF ( Nothing :< LitF True ) ( Just False :< LitF False ) )
-- >> pPrint $ quiet . why . withEval $ ex
-- > Just False :< MaybeT
-- >   ( AndF Nothing
-- >          ( Just ( Just False :< MaybeT
-- >                   ( AndF Nothing
-- >                     ( Just ( Just False :< MaybeT ( LitF False ) ) ) ) ) ) )
quiet ∷ Cofree FormulaF (Maybe Bool) → Cofree (MaybeT FormulaF) (Maybe Bool)
quiet = apo quietRCoalg

quietRCoalg ∷
    Cofree FormulaF (Maybe Bool)
  → CofreeF (MaybeT FormulaF)
            (Maybe Bool)
            (Either (Cofree (MaybeT FormulaF) (Maybe Bool))
                    (Cofree FormulaF (Maybe Bool)))
quietRCoalg t@(Nothing :< _) = bimapCF id (MaybeT ∘ fmap (const Nothing ∘ Left)) t
quietRCoalg t@(Just _  :< _) = bimapCF id (MaybeT ∘ fmap (fmap Right ∘ justWhen (isJust ∘ extract))) t


-- -- TODO this is marginally useful.
-- -- | Replace 'Nothing', 'Just False', and 'Just True' annotations (respectively)
-- -- with the provided values.
-- --
-- -- == Example
-- --
-- -- >> leftBranch = (true && true) :: Formula
-- -- >> rightBranch = (true && false) :: Formula
-- -- >> ex = leftBranch && rightBranch
-- -- >> pPrint ex
-- -- > And
-- -- >   ( And ( Lit True ) ( Lit True  ) )
-- -- >   ( And ( Lit True ) ( Lit False ) )
-- -- >> pPrint $ why . withEval $ ex
-- -- > Just False :< AndF
-- -- >     ( Nothing    :< AndF ( Nothing :< LitF True ) ( Nothing    :< LitF True  ) )
-- -- >     ( Just False :< AndF ( Nothing :< LitF True ) ( Just False :< LitF False ) )
-- -- >> pPrint $ quiet . why . withEval $ ex
-- -- > Just False :< MaybeT
-- -- >   ( AndF Nothing
-- -- >          ( Just ( Just False :< MaybeT
-- -- >                   ( AndF Nothing
-- -- >                     ( Just ( Just False :< MaybeT ( LitF False ) ) ) ) ) ) )
-- -- >> pPrint $ fmap (quietEval '_' 'F' 'T') $ quiet . why . withEval $ ex
-- -- > 'F' :< MaybeT
-- -- >   ( AndF Nothing
-- -- >     ( Just
-- -- >       ( 'F' :< MaybeT
-- -- >         ( AndF Nothing
-- -- >           ( Just
-- -- >             ( 'F' :< MaybeT ( LitF False ) ) ) ) ) ) )
-- quietEval ∷ ∀ a.
--    a → a → a
--  → Maybe Bool → a
-- quietEval n _ _ Nothing      = n
-- quietEval _ f _ (Just False) = f
-- quietEval _ _ t (Just True)  = t



-- | A mildly less verbose variant of 'quiet' that can only be safely run on
-- values whose (outermost) annotation is 'Just True' or 'Just False':
-- conditioned on this assumption holding, 'Maybe's can be stripped from each
-- layer of annotation.
--
-- The main intended use case for this variant is interactive debugging. Use
-- with discretion.
--
-- == Example
--
-- >> leftBranch = (true && true) :: Formula
-- >> rightBranch = (true && false) :: Formula
-- >> ex = leftBranch && rightBranch
-- >> pPrint ex
-- > And
-- >   ( And ( Lit True ) ( Lit True  ) )
-- >   ( And ( Lit True ) ( Lit False ) )
-- >> pPrint $ why . withEval $ ex
-- > Just False :< AndF
-- >     ( Nothing    :< AndF ( Nothing :< LitF True ) ( Nothing    :< LitF True  ) )
-- >     ( Just False :< AndF ( Nothing :< LitF True ) ( Just False :< LitF False ) )
-- >> pPrint $ quiet . why . withEval $ ex
-- > Just False :< MaybeT
-- >   ( AndF Nothing
-- >      ( Just ( Just False :< MaybeT
-- >               ( AndF Nothing
-- >                 ( Just ( Just False :< MaybeT ( LitF False ) ) ) ) ) ) )
-- >> pPrint $ quietUnsafe . why . withEval $ ex
-- > False :< MaybeT
-- >   ( AndF Nothing
-- >     ( Just ( False :< MaybeT
-- >       ( AndF Nothing
-- >         ( Just ( False :< MaybeT ( LitF False ) ) ) ) ) ) )
quietUnsafe ∷ Cofree FormulaF (Maybe Bool) → Cofree (MaybeT FormulaF) Bool
quietUnsafe = apo quietRCoalgUnsafe

quietRCoalgUnsafe ∷
    Cofree FormulaF (Maybe Bool)
  → CofreeF (MaybeT FormulaF)
            Bool
            (Either (Cofree (MaybeT FormulaF) Bool)
                    (Cofree FormulaF (Maybe Bool)))
quietRCoalgUnsafe t@(Just _  :< _)
  = bimapCF fromJust (MaybeT ∘ fmap (fmap Right ∘ justWhen (isJust ∘ extract))) t
quietRCoalgUnsafe   (Nothing :< _)
  = error "Error: called 'quietRCoalgUnsafe' on a formula with an empty annotation."



