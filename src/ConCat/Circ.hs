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

import Data.Vector.Sized (Vector)
import Data.Constraint

-- This is what a morphism looks like in LCirc
data RLC = Res R
  | Cap R
  | Ind R
  deriving (Eq, Ord, Show, Generic)


instance HasRep (RLC) where
  type Rep (RLC) = (Maybe R, Maybe R, Maybe R)
  abst (Just r, Nothing, Nothing) = Res r
  abst (Nothing, Just c, Nothing) = Cap c
  abst (Nothing, Nothing, Just i) = Ind i
  repr (Res r) = (Just r, Nothing, Nothing)
  repr (Cap c) = (Nothing, Just c, Nothing)
  repr (Ind i) = (Nothing, Nothing, Just i)


instance HasV R (Maybe R) where
  type V R (Maybe R) = Maybe :.: V R R
  toV = Comp1 . fmap toV
  unV = fmap unV . unComp1

instance HasV R (RLC)

instance GenBuses (RLC) where
  genBuses' = genBusesRep'
  ty = tyRep @RLC
  unflattenB' = genUnflattenB'

type RLCTemplate = Template RLC RLC

newtype LCirc i o = LC { unLC :: RLC :> RLC }

blackbox :: (RLC :> RLC) -> Affine R R R :> Affine R R R
blackbox = undefined

newtype Blackbox a = Blackbox a deriving (Eq, Ord, Functor, Generic)

instance (HasRep a) => HasRep (Blackbox a) where
  type Rep (Blackbox a) = a
  abst = Blackbox
  repr (Blackbox a) = a

instance (GenBuses a) => GenBuses (Blackbox a) where
  genBuses' = genBusesRep'
  ty = tyRep @(Blackbox a)
  unflattenB' = genUnflattenB'

instance OkFunctor (:>) (Blackbox) where
  okFunctor = Entail (Sub Dict)

--instance FunctorCat (:>) (Blackbox)
