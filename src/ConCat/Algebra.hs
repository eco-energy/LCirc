{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module ConCat.Algebra where

import qualified ConCat.ADFun as AD
import qualified ConCat.AD as AD
import qualified ConCat.Free.Affine as A
import qualified ConCat.Free.LinearRow as R
import qualified ConCat.Free.VectorSpace as V
import qualified ConCat.Incremental as I
import qualified ConCat.Rep as R
import ConCat.Rebox ()
import ConCat.AltCat ()
import ConCat.Choice
import ConCat.Distribution
import GHC.Generics (Generic)
import ConCat.Misc hiding (R)

-- s is a container type, a is a container and b is the contained? 
--type Objective s a r = V.V s a b

-- incremental state
data Kibutz s a r where
  State :: s -> Kibutz s () ()
  Action :: (s -> a) -> Kibutz s () () -> Kibutz s a () 
  Reward :: (s -> a -> r) -> Kibutz s a () -> Kibutz s a r
  T :: s -> a -> r -> (Kibutz s a r)

instance R.HasRep (Kibutz s a r) where
  type Rep (Kibutz s a r) = (s, a, r)
  abst (s, a, r) = (T s a r)
  repr (T s a r) = (s, a, r)
  repr (State s) = (s, (), ())
  repr (Action act (State s)) = (s, (act s), ())
  repr (Reward rew (Action act (State s))) = (s, act s, rew s (act s))


type R = Double

type KV f s a r = V.RepHasV f (Kibutz s a r)

type KVs s a r = KV [R] s a r

type RKVs = KVs R R R

--test :: (V.HasV r s, V.HasV r a, V.HasV r r) => s -> a -> r -> V.V s a r
test s a r = (V.toV s, V.toV a, V.toV r) 

instance (V.HasV f s, V.HasV f a, V.HasV f r) => V.HasV f (Kibutz s a r) where
  toV = undefined
  unV = undefined

data K' s a r = S' s () ()
  | A' s a () 
  | R' s a r
  deriving (Generic)

state :: s -> Kibutz s () ()
state = State

action :: (pa -> s -> a) -> pa -> Kibutz s () () -> Kibutz s a ()
action act params = Action (act params)

reward :: (pr -> s -> a -> r) -> pr -> Kibutz s a () -> Kibutz s a r
reward r params = Reward (r params)

mkT = T

learn :: (Num s, Num a, Num r) => s -> (pa -> s -> a) -> (pr -> s -> a -> r) -> pa -> pr -> Kibutz s a r
learn s a r pa pr = (reward r pr) . (action a pa) . state $ s

-- the gradient is described over a field f,
-- via a linspace representation formed over
-- it by a containerization within
-- s and a.
--gradF' :: forall s a b. (V.HasV s a) => (a -> s) -> a -> a
--gradF' = AD.gradF
