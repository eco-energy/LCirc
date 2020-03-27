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

import Prelude hiding ((.), id, const)
import qualified ConCat.ADFun as AD
import qualified ConCat.AD as AD
import qualified ConCat.GAD as AD
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
import ConCat.Category

-- s is a container type, a is a container and b is the contained? 
--type Objective s a r = V.V s a b

-- incremental state
data Kibutz r s a where
  State :: (s -> a -> s) -> s -> Kibutz () s ()
  Action :: (s -> a) -> Kibutz () s () -> Kibutz () s a 
  Reward :: (s -> a -> r) -> Kibutz () s a -> Kibutz r s a
  T :: r -> s -> a -> (Kibutz r s a)

instance R.HasRep (Kibutz r s a) where
  type Rep (Kibutz r s a) = (r, s, a)
  abst (r, s, a) = (T r s a)
  repr (T r s a) = (r, s, a)
  repr (State s' s) = ((), s, ())
  repr (Action act (State s' s)) = ((), s, (act s))
  repr (Reward rew (Action act (State s' s))) = (rew s (act s), s, act s)


type R = Double

type KV f r s a = V.RepHasV f (Kibutz r s a)

type KVs r s a = KV [R] r s a

type RKVs = KVs R R R

--test :: (V.HasV r s, V.HasV r a, V.HasV r r) => s -> a -> r -> V.V r s a
test r s a = (V.toV s, V.toV a, V.toV r) 

instance (V.HasV f s, V.HasV f a, V.HasV f r) => V.HasV f (Kibutz r s a) where
  toV = undefined
  unV = undefined

data K' r s a = S' s () ()
  | A' s a () 
  | R' r s a
  deriving (Generic)

state :: s -> Kibutz () s ()
state = State $ const id

action :: (pa -> s -> a) -> pa -> Kibutz () s () -> Kibutz () s a
action act params = Action (act params)

reward :: (pr -> s -> a -> r) -> pr -> Kibutz () s a -> Kibutz r s a
reward r params = Reward (r params)

mkT = T

learn :: (Num s, Num a, Num r) => (pr -> s -> a -> r) -> s -> (pa -> s -> a) ->  pa -> pr -> (Kibutz r s a, pa, pr)
learn r s a pa pr = (k, pa, pr)
  where
    k = (reward r pr) . (action a pa) . state $ s




-- derivative of the reward with respect to the action
-- TODO: If I can add pa and pr to Kibutz then dpa will allow me to
-- update the weights as well.
dpa
  :: (pr -> s -> a -> r)
     -> (pa -> s -> a)
     -> s
     -> pr
     -> pa
     -- this type-signature is broken to be fixed.
     -- remove pa () from the first deriv and pa pr from the second
     -> Kibutz r s a :* R.L s (Kibutz () s a pa ()) (Kibutz r s a pa pr)
dpa r a s pr pa = AD.andDer (reward r pr) (action a pa $ state s)
    


{--
There is a category instance here where a morphism
is from Kibutz r s a -> Kibutz r s' a'
instance Category (Kibutz r) where
  id = id
  (State sn s) . (State sn' s') = State $ sn' s'
  (State sn s') . (Action act s) = Action act s'
    where
      s'' = sn (act s')
--}
