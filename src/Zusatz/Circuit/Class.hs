{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StarIsType #-}
-- |

module Zusatz.Circuit.Class where

-- import Prelude qualified as P
import Prelude hiding
  ( id
  , (.)
  , fst
  , snd
  , curry
  , uncurry
  , const
  )

import Control.Category.Constrained
  ( Category ( Object
             , id
             , (.)
             )
  , Cartesian ( PairObjects
              , UnitObject
              , swap
              , attachUnit
              , detachUnit
              , regroup
              , regroup'
              )
  , ObjectPair
  , Curry ( MorphObjects
          , uncurry
          , curry
          , apply
          )
  , type (+)
  , CoCartesian ( SumObjects
                , ZeroObject
                , coSwap
                , attachZero
                , detachZero
                , coRegroup
                , coRegroup'
                , maybeAsSum
                , maybeFromSum
                , boolAsSum
                , boolFromSum
                )
  , ObjectSum
  , HasAgent ( AgentVal
             , alg
             , ($~)
             )
  )
import Control.Arrow.Constrained
  ( Morphism ( (***)
             , first
             , second
             )
  , PreArrow ( (&&&)    -- (△)
             , fst      -- exl
             , snd      -- exr
             , terminal -- it
             )
  , WellPointed ( PointObject
                , globalElement -- unitArrow
                , unit
                , const         -- const
                )
  , ObjectPoint
  , MorphChoice ( (+++)
                , left
                , right
                )
  , PreArrChoice ( (|||) -- (▽)
                 , coFst -- inl
                 , coSnd -- inr
                 )
  , SPDistribute ( distribute   -- distl
                 , unDistribute -- distr
                 , boolAsSwitch
                 , boolFromSwitch
                 )
  , (>>>)
  , (<<<)
  , choose
  , ifThenElse
  )
import Control.Applicative (liftA2)
import Control.Monad ((<=<))
import Control.Monad.State (State, get, put, modify)

class PreArrow k ⇒ BoolCat k where
  notC ∷ Bool `k` Bool
  andC, orC, xorC, impliesC, iffC, nandC, norC ∷ Bool `k` Bool


-- TODO move this to Zusatz.Circuit.Graph

data Graph a b = Graph (Ports a → GraphM (Ports b))

type GraphM = State (Port, [Comp])

data Comp = ∀ a b. Comp String (Ports a) (Ports b)

type Port = Int

data Ports ∷ * → * where
  UnitP   ∷ Ports ()
  BoolP   ∷ Port → Ports Bool
  IntP    ∷ Port → Ports Int
  DoubleP ∷ Port → Ports Double
  PairP   ∷ Ports a → Ports b → Ports (a,b)
  FunP    ∷ Graph a b → Ports (a → b)

instance Category Graph where
  type Object Graph a = GenPorts a

  id = Graph return

  Graph g . Graph f = Graph (g <=< f)


-- TODO
instance Cartesian Graph where
  swap ∷ (a, b) `k` (b, a)
  swap = undefined

  attachUnit ∷ a `k` (a, UnitObject Graph)
  attachUnit = undefined

  detachUnit ∷ (a, UnitObject k) `k` a
  detachUnit = undefined

  regroup ∷ (a, (b, c)) `k` ((a, b), c)
  regroup = undefined

  regroup' ∷ ((a, b), c) `k` (a, (b, c))
  regroup' = undefined


-- TODO
instance Morphism Graph where
  (***) ∷ a b c → a b' c' → a (b, b') (c, c')
  (Graph f) *** (Graph g) = undefined

-- TODO
-- instance PreArrow Graph where
--   fst = Graph (\(PairP a _) → return a)
--   snd = Graph (\(PairP _ b) → return b)

--   (Graph f) &&& (Graph g) = Graph (liftA2 (liftA2 PairP) f g)

--   terminal = Graph (P.const (return UnitP))


genPort ∷ GraphM Port
genPort = do
  (o, comps) ← get
  put (o + 1, comps)
  return o

class GenPorts a where
  genPorts ∷ GraphM (Ports a)

instance GenPorts ()     where genPorts = return UnitP
instance GenPorts Bool   where genPorts = fmap BoolP   genPort
instance GenPorts Int    where genPorts = fmap IntP    genPort
instance GenPorts Double where genPorts = fmap DoubleP genPort
instance (GenPorts a, GenPorts b) ⇒ GenPorts (a,b)
  where genPorts = liftA2 PairP genPorts genPorts

genComp ∷ GenPorts b ⇒ String → Graph a b
genComp name =
  Graph (\a → do
           b ← genPorts
           modify (second (Comp name a b :))
           return b)

-- TODO
-- instance BoolCat Graph where
--   notC = genComp "¬"
--   andC = genComp "∧"
--   orC = genComp "∨"
--   xorC = genComp "⊕"
--   impliesC = genComp "⇒"
--   iffC = genComp "≡"
--   nandC = genComp "↑"
--   norC  = genComp "↓"



-- TODO
-- graphviz utils for rendering circuits



-- TODO connection to 'Formula' +/- ersatz's 'Boolean'
