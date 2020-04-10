{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# Language TypeOperators, TypeApplications, ScopedTypeVariables #-}

module ConCat.Circ where

import Prelude hiding ((.), id, curry, uncurry, const)
import ConCat.Circuit ( CircuitM, (:>)
  , Bus(..),Comp(..),Input,Output, Ty(..), busTy, Source(..), Template(..)
  , GenBuses(..), GS, genBusesRep', tyRep
  -- , delayCRep, unDelayName
  , namedC, constC -- , constS
  , genUnflattenB'
  , SourceToBuses(..), CompS(..), simpleComp
  , mkGraph
  , Attr
  , graphDot, writeDot, displayDot,Name,Report,Graph
  -- , simpleComp
  , tagged
  , systemSuccess
  -- For AbsTy
  , BusesM, abstB,abstC,reprC,Buses(..)
  , OkCAR
  -- , Ty(..)
  )
import GHC.Generics (unComp1, (:.:)(..), Generic)

import ConCat.Misc
import qualified ConCat.RunCircuit as RC
import ConCat.Rep
import ConCat.Category

import ConCat.AltCat ()
import ConCat.Rebox () -- necessary for reboxing rules to fire
import ConCat.Orphans ()
import ConCat.Free.VectorSpace
import ConCat.Free.Affine
import ConCat.Free.LinearRow
import ConCat.Additive

import Data.Vector.Sized (Vector)
import Data.Constraint
import Data.Complex
import Data.Key


-- This is what a morphism looks like in LCirc
data RLC a = Res a
  | Cap a
  | Ind a
  deriving (Eq, Show, Functor, Generic)


instance (HasRep a) => HasRep (RLC a) where
  type Rep (RLC a) = (Maybe a, Maybe a, Maybe a)
  abst (Just r, Nothing, Nothing) = Res r
  abst (Nothing, Just c, Nothing) = Cap c
  abst (Nothing, Nothing, Just i) = Ind i
  repr (Res r) = (Just r, Nothing, Nothing)
  repr (Cap c) = (Nothing, Just c, Nothing)
  repr (Ind i) = (Nothing, Nothing, Just i)


instance (HasV R a) => HasV R (Maybe a) where
  type V R (Maybe a) = Maybe :.: V R a
  toV = Comp1 . fmap toV
  unV = fmap unV . unComp1

instance (HasV R a) => HasV R (Complex a)

instance (HasRep a, HasV R a) => HasV R (RLC a)

instance (GenBuses a) => GenBuses (RLC a) where
  genBuses' = genBusesRep'
  ty = tyRep @(RLC a)
  unflattenB' = genUnflattenB'


newtype VI a = VI (a, a) deriving (Eq, Ord, Generic)

instance HasRep a => HasRep (VI a) where
  type Rep (VI a) = (a, a)
  repr (VI (v, i)) = (v, i)
  abst = VI

instance (GenBuses a) => GenBuses (VI a) where
  genBuses' = genBusesRep'
  ty = tyRep @(VI a)
  unflattenB' = genUnflattenB'

instance (HasRep a, HasV R a) => HasV R (VI a)

--elem :: VI' :> RLC
--elem = namedC "elem"

type VI' = VI R

type LC a = (VI a, RLC a)

-- laplace transform all the tings

--class Circ i b where
--  codup :: (Num b) => (LC b :* LC b) -> (LC b) -> (LC b)
--  dup :: (Num b) => (LC b) -> ((LC b) :* (LC b))
--  unit :: (Num b) => () -> (LC b)
--  counit :: (Num b) => (LC b) -> ()


blackbox :: Fractional a => (VI a) -> (RLC a) -> (VI a)
blackbox (VI (v,i)) (Res r) = VI (v + r*i, i)
blackbox (VI (v,i)) (Cap c) = VI (v + (i / c), i)
blackbox (VI (v, i)) (Ind l) = VI (v + (l * i), i)

--bb :: (Fractional b) => Circ a -> VI b
--bb (Codup (lc1, lc2) lc3) = (uncurry blackbox $ lc1)

--blackbox :: (RLC :> RLC) -> Affine R R R
--blackbox = undefined

newtype Blackbox a = Blackbox (L R a R) deriving (Generic)


instance (HasRep a) => HasRep (Blackbox a) where
  type Rep (Blackbox a) = a
  abst = undefined $ Blackbox
  repr (Blackbox a) = undefined $ a

instance (GenBuses a) => GenBuses (Blackbox a) where
  genBuses' = genBusesRep'
  ty = tyRep @(Blackbox a)
  unflattenB' = genUnflattenB'

instance OkFunctor (:>) (Blackbox) where
  okFunctor = Entail (Sub Dict)


