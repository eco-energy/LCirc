{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
module Exp where

import Algebra.Graph.Labelled
import qualified Algebra.Graph.Labelled.AdjacencyMap as AM

import Prelude hiding ((.), id)

import GHC.Generics (Generic)
import ConCat.Category
import ConCat.Misc
import ConCat.TArr
import Data.Bifunctor
import Data.Map.Strict (Map(..))
import qualified Data.Map.Strict as Map


data Node = Node
  { v :: R,
    i :: R,
    n :: Int
  } deriving (Eq, Ord, Show)


-- This is what a morphism looks like in LCirc
data El a = Res a
  | Cap a
  | Ind a
  | Parallel (El a) (El a)
  deriving (Eq, Ord, Show, Generic)

data Ci a where
  Join :: a -> a -> Ci (a :* a)
  Split :: a -> Ci (a :* a)
  Start :: a -> Ci a
  End :: a -> Ci ()


type CiRLC = Ci (El R)

instance Semigroup (El a) where
  a <> b = Parallel a b

instance (Num a) => Monoid (El a) where
  mempty = Res 0

newtype LGraph = LGraph (Graph (El R) Node)
  deriving (Eq, Ord, Generic)

newtype Cospan i o = Cospan { unCospan :: (Arr i [Node]) :* (Arr o [Node]) }
-- We need a functor to go from
-- LGraph -> Cosp
inputs :: Cospan i o -> Arr i [Node]
inputs = fst . unCospan

outputs :: Cospan i o -> Arr o [Node]
outputs = snd . unCospan

composeCospan :: Cospan i o -> Cospan o o' -> (Cospan i o', Arr o (Node, Node))
composeCospan c@(Cospan (i, o)) c'@(Cospan (i', o')) = (Cospan (i, o'), apex)
  where
    apex = undefined


-- Circ is a morphism in the category LCirc, and the objects
-- are sets of Natural Numbers, here represented by i o
newtype Circ i o = Circ { unCirc :: (LGraph, Cospan i o) } 



type Merger o = Arr o Node -> Arr o Node -> Arr o (Node, Node)

mergeP :: Merger o
mergeP o i' = undefined -- fmap o i'

-- We need an empty cospan to define the Id on Circ

instance Category Circ where
  type Ok Circ = HasFin
  id = id
  (Circ c) . (Circ c') = undefined
  
-- Let Circ be a symmetric Monoidal Category
-- a morphism in Circ is an isomorphism class X -i> N <o- Y
-- of cospans of finite sets, together with a graph
-- T having N as its set of vertices
