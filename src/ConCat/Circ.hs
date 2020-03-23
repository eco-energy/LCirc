{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# Language TypeOperators, TypeApplications, ScopedTypeVariables #-}

module ConCat.Circ where

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


import qualified ConCat.Circuit as C
import qualified ConCat.RunCircuit as RC
import ConCat.Deep
import ConCat.Free.VectorSpace (HasV(..), distSqr, (<.>), normalizeV)
import qualified ConCat.AltCat as A

import ConCat.Rebox () -- necessary for reboxing rules to fire
import ConCat.Orphans ()
import ConCat.Nat
import ConCat.Shaped

import ConCat.Free.LinearRow
import ConCat.Isomorphism
import ConCat.Free.Affine
import ConCat.Chain
import ConCat.Choice
import ConCat.Free.VectorSpace
import Data.Vector.Sized (Vector)

import ConCat.Utils
import ConCat.LCirc (CircEl(..), LG(..), Edge(..), VI(..), LCirc'(..), R, CospanC(..))




a = runCirc "affRelu" $ A.toCcc $ affRelu @(Vector 2) @(Vector 3) @R

instance GenBuses VI where
  genBuses' = genBusesRep'
  ty = tyRep @VI
  unflattenB' = genUnflattenB'

instance GenBuses CircEl where
  genBuses' = genBusesRep'
  ty = tyRep @CircEl
  unflattenB' = genUnflattenB'

instance (GenBuses l, GenBuses v) => GenBuses (Edge l v) where
  genBuses' = genBusesRep'
  ty = tyRep @ (Edge l v)
  unflattenB' = genUnflattenB'

instance (GenBuses l, GenBuses v) => GenBuses (LG l v) where
  genBuses' = genBusesRep'
  ty = tyRep @ (LG l v)
  unflattenB' = genUnflattenB'


instance GenBuses (CospanC v i o) where
  genBuses' = genBusesRep'
  ty = tyRep @ (CospanC v i o)
  unflattenB' = genUnflattenB'

instance GenBuses (LCirc' i o) where
  genBuses' = genBusesRep'
  ty = tyRep @ (LCirc' i o)
  unflattenB' = genUnflattenB'


--runCirc :: GO a b => String -> (a :> b) -> IO ()
-- type GO a b = (GenBuses a, Ok2 (:>) a b)


rc :: (CircEl :> VI) -> IO ()
rc = runCirc "name" 

rcR1 = undefined
