{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeOperators #-}
-- |

module Zusatz.Circuit.Class where

import Prelude qualified as P
import Prelude hiding
  ( id
  , (.)
  , fst
  , snd
  , curry
  , uncurry
  , const
  , foldMap
  )

import Control.Applicative (liftA2)
import Control.Monad ((<=<))
import Control.Monad.State (State, get, put, modify)

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
  , ObjectMorphism
  -- , type (+)
  -- , CoCartesian ( SumObjects
  --               , ZeroObject
  --               , coSwap
  --               , attachZero
  --               , detachZero
  --               , coRegroup
  --               , coRegroup'
  --               , maybeAsSum
  --               , maybeFromSum
  --               , boolAsSum
  --               , boolFromSum
  --               )
  -- , ObjectSum
  -- , HasAgent ( AgentVal
  --            , alg
  --            , ($~)
  --            )
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
  -- , WellPointed ( PointObject
  --               , globalElement -- unitArrow
  --               , unit
  --               , const         -- const
  --               )
  -- , ObjectPoint
  -- , MorphChoice ( (+++)
  --               , left
  --               , right
  --               )
  -- , PreArrChoice ( (|||) -- (▽)
  --                , coFst -- inl
  --                , coSnd -- inr
  --                )
  -- , SPDistribute ( distribute   -- distl
  --                , unDistribute -- distr
  --                , boolAsSwitch
  --                , boolFromSwitch
  --                )
  -- , (>>>)
  -- , (<<<)
  -- , choose
  -- , ifThenElse
  )



class (PreArrow k)
  ⇒ BoolCat k where
  notC ∷ (Object k a) ⇒ a `k` a
  andC, orC, xorC, impliesC, iffC, nandC, norC ∷
    (Object k a, Object k (a,a), PairObjects k a a) ⇒ (a, a) `k` a

  andC     = notC . orC  . (notC *** notC)
  orC      = notC . andC . (notC *** notC)
  xorC     = andC . (orC &&& notC . andC)
  impliesC = orC  . first notC
  iffC     = andC . (impliesC &&& impliesC . swap)
  nandC    = notC . andC
  norC     = notC . orC
  {-# MINIMAL (notC, andC) | (notC, orC) #-}

-- class (PreArrow k)
--   ⇒ BoolCat k where
--   notC ∷ (Object k a, Object k b) ⇒ a `k` b
--   andC, orC, xorC, impliesC, iffC, nandC, norC ∷
--     (Object k a, Object k (a,b), PairObjects k a b, SumObjects k a b) ⇒ (a, b) `k` (a + b)

--   andC     = notC . orC  . (notC *** notC)
--   orC      = notC . andC . (notC *** notC)
--   xorC     = andC . (orC &&& notC . andC)
--   impliesC = orC  . first notC
--   iffC     = andC . (impliesC &&& impliesC . swap)
--   nandC    = notC . andC
--   norC     = notC . orC
--   {-# MINIMAL (notC, andC) | (notC, orC) #-}


-- TODO move this to Zusatz.Circuit.Graph

data Graph a b = Graph { unGraph ∷ Ports a → GraphM (Ports b)}

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

instance Cartesian Graph where
  swap ∷ (ObjectPair Graph a b, ObjectPair Graph b a)
       ⇒ (a, b) `Graph` (b, a)
  swap = (id . snd) &&& (id . fst)

  attachUnit ∷ (ObjectPair Graph a ())
             ⇒ a `Graph` (a, ())
  attachUnit = id &&& terminal

  detachUnit ∷ (ObjectPair Graph a ())
             ⇒ (a, ()) `Graph` a
  detachUnit = id . fst

  regroup ∷ ( ObjectPair Graph a b    , ObjectPair Graph b     c
            , ObjectPair Graph a (b,c), ObjectPair Graph (a,b) c)
          ⇒ (a, (b, c)) `Graph` ((a, b), c)
  regroup = (fst &&& (fst . snd)) &&& (snd . snd)

  regroup' ∷ ( ObjectPair Graph a b    , ObjectPair Graph b     c
             , ObjectPair Graph a (b,c), ObjectPair Graph (a,b) c)
           ⇒ ((a, b), c) `Graph` (a, (b, c))
  regroup' = (fst . fst) &&& ((snd . fst) &&& snd)

instance Morphism Graph where
  (***) ∷ (ObjectPair Graph a a', ObjectPair Graph b b')
        ⇒ a `Graph` b → a' `Graph` b' → (a, a') `Graph` (b, b')
  f *** g = (f . fst) &&& (g . snd)

instance PreArrow Graph where
  fst ∷ ObjectPair Graph a b
      ⇒ (a,b) `Graph` a
  fst = Graph (\(PairP a _) → return a)

  snd ∷ ObjectPair Graph a b
      ⇒ (a,b) `Graph` b
  snd = Graph (\(PairP _ b) → return b)

  (&&&) ∷ a `Graph` b → a `Graph` b' -> a `Graph` (b, b')
  (Graph f) &&& (Graph g) = Graph (liftA2 (liftA2 PairP) f g)

  terminal ∷ a `Graph` ()
  terminal = Graph (P.const (return UnitP))

-- instance Curry Graph where
--   uncurry ∷ (ObjectPair Graph a b)
--          ⇒ a `Graph` (b `Graph` c) → (a, b) `Graph` c
--   -- uncurry = undefined
--   uncurry = undefined
--   -- uncurry (Graph g) = Graph (\(PairP a b) → do {FunP (Graph f) ← g a ; f b})
-- --   -- uncurry (Graph g) = Graph (\(PairP a b) → do $
-- --   --                                             FunP (Graph f) ← g a
-- --   --                                             f b)
--   -- curry ∷ (ObjectPair Graph a b)
--   --       ⇒ (a, b) `Graph` c → a `Graph` (b `Graph` c)
--   -- curry = undefined
--   -- curry (Graph f) = Graph (\a → )

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

instance BoolCat Graph where
  notC     = genComp "¬"
  andC     = genComp "∧"
  orC      = genComp "∨"
  xorC     = genComp "⊕"
  impliesC = genComp "⇒"
  iffC     = genComp "≡"
  nandC    = genComp "↑"
  norC     = genComp "↓"



-- TODO
-- graphviz utils for rendering circuits



-- TODO connection to 'Formula' +/- ersatz's 'Boolean'
