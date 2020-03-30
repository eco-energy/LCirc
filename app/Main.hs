{-# LANGUAGE DataKinds #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -fplugin=ConCat.Plugin #-}
{-# OPTIONS_GHC -O2 #-}
-- {-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:trace #-}
{-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:showResiduals #-}
-- {-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:showCcc #-}


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
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Data.Key

import Prelude hiding ((.), id, const)
import qualified ConCat.RAD as AD
import qualified ConCat.Free.Affine as A
import qualified ConCat.Free.LinearRow as R
import qualified ConCat.Free.VectorSpace as V
import qualified ConCat.Incremental as I
import qualified ConCat.Rep as R
import ConCat.Rebox ()
import ConCat.AltCat ()

import ConCat.Choice
import ConCat.Distribution
import GHC.Generics hiding (R)
import ConCat.Misc hiding (R)
import ConCat.Category
import ConCat.Deep

import ConCat.TArr


type PConn a b c d = (C3 Foldable a b c, C3 Zip a b c, C3 Functor b c d)

--type PType f = forall f s. (Functor f, Foldable f, Zip f) => (f --+ f) :*: (f s --+ f s) s

-- s is a container type, a is a container and b is the contained? 
--type Objective s a r = V.V s a b

-- incremental state
data Kibutz r s a where
  State :: (s -> a -> s) -> s -> Kibutz () s ()
  Action :: (s -> a) -> Kibutz () s () -> Kibutz () s a
  Reward :: (s -> a -> r) -> Kibutz () s a -> Kibutz r s a
  T :: r -> s -> a -> (Kibutz r s a)


instance (Show r, Show s, Show a) => Show (Kibutz r s a) where
  show (State _ s) = show s
  show (Action a' (State _ s)) = show (a' s)
  show (Reward r' a@(Action a' (State _ s))) = show (r' s $ a' s)
  show (T r s a) = show (r, s, a)

instance R.HasRep (Kibutz r s a) where
  type Rep (Kibutz r s a) = (r, s, a)
  abst (r, s, a) = (T r s a)
  repr (T r s a) = (r, s, a)
  repr (State s' s) = ((), s, ())
  repr (Action act (State s' s)) = ((), s, (act s))
  repr (Reward rew (Action act (State s' s))) = (rew s (act s), s, act s)

class Trainable (k :: * -> * -> *) b c where
  
  

type R = Double

type KV f r s a = V.RepHasV f (Kibutz r s a)

type KVs r s a = KV [R] r s a

type RKVs = KVs R R R

 --(V.HasV r s, V.HasV r a, V.HasV r r) => s -> a -> r -> V.V r s a
test r s a = (V.toV s, V.toV a, V.toV r) 

instance (V.HasV R s, V.HasV R a, V.HasV R r) => V.HasV R (Kibutz r s a) where
  toV :: Kibutz r s a -> V.V R (Kibutz r s a) R
  toV (State s' s) = undefined
  unV = undefined

data K' r s a = S' s () ()
  | A' s a () 
  | R' r s a
  deriving (Generic)

state :: s -> Kibutz () s ()
state = State $ const id
{-# INLINE state #-}

action :: (pa -> s -> a) -> pa -> Kibutz () s () -> Kibutz () s a
action = \act params -> Action (act params)
{-# INLINE action #-}

reward :: (pr -> s -> a -> r) -> pr -> Kibutz () s a -> Kibutz r s a
reward = \r params -> Reward (r params)
{-# INLINE reward #-}

r :: Kibutz r s a -> r
r (Reward r (Action act (State _ s))) = r s (act s)

an :: forall r s a. Kibutz r s a -> a
an (Reward r (Action act (State _ s))) = act s

{--
sn :: Kibutz r s a -> s
sn (Reward r (Action act s''@(State s' s))) = s' s (act s)
--}

mkT = T

step' :: forall s a r pr pa. (Num s, Num a, Num r) => (pr -> s -> a -> r) -> s -> (pa -> s -> a) ->  pa -> pr -> Kibutz r s a
step' = \ r s a pa pr -> (reward r pr) . (action a pa) . state $ s
{-# INLINE step' #-}

l' :: (R -> R -> R -> R) -> R -> (R -> R -> R) -> R -> R -> Kibutz R R R
l' = step'

r' :: R -> R -> R -> R
r' params st ac = params * ac * st
{-# INLINE r' #-}

a' :: R -> R -> R
a' params s = (params + s)^2
{-# INLINE a' #-}

s' = 99 :: R

pr' = 7 :: R

pa' = 2 :: R



--dpa' :: (Kibutz R R R :* R.L R (Kibutz () R R) (Kibutz R R R))
l'' = l' r' s' a'

dpr' = AD.andGradR (r . (l'' pa')) pr'

dpa' = AD.andGradR (an . (flip l'') pr') pa'

{-# INLINE dpa' #-}

main = do
  print $ "reward gradient wrt reward params" <> (show dpr')
  print $ "action gradient wrt action params" <> (show dpa')
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

{--
Probability Density Distillation, a new method for
training a parallel feed-forward network from a trained WaveNet with no significant
difference in quality
--}


-- Wavenet
-- autoregressive deep generative model
-- 
