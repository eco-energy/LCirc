{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}
module Exp where

import Algebra.Graph.Labelled
import qualified Algebra.Graph.Labelled.AdjacencyMap as AM

import Prelude hiding ((.), id)

import GHC.Generics (Generic)
import ConCat.Category
import ConCat.Misc
import ConCat.TArr
import Data.Bifunctor



data Node = Node
  { v :: R,
    i :: R,
    n :: Int
  } deriving (Eq, Ord, Show)


-- This is what a morphism looks like in LCirc
data El = Res R
  | Cap R
  | Ind R
  | Series El El
  | Parallel El El
  deriving (Eq, Ord, Show, Generic)

class Ci a where
  join :: (a :* a) -> a
  split :: a -> (a :* a)
  start :: a -> a
  end :: a -> ()


-- We choose the semigroup to be
-- parallel because series composition
-- must obey pushout laws
instance Semigroup El where
  a <> b = Parallel a b

instance Monoid El where
  mempty = Res 0

newtype LGraph = LGraph (Graph El Node)
  deriving (Eq, Ord, Generic)

newtype Cospan i o = Cospan { unCospan :: (Arr i Node) :* (Arr o Node) }
-- We need a functor to go from
-- LGraph -> Cosp
inputs :: Cospan i o -> Arr i Node
inputs = fst . unCospan

outputs :: Cospan i o -> Arr o Node
outputs = snd . unCospan

composeCospan :: Cospan i o -> Cospan o o' -> (Cospan i o', Arr o (Node, Node))
composeCospan c@(Cospan (i, o)) c'@(Cospan (i', o')) = (Cospan (i, o'), apex)
  where
    apex = undefined

newtype Circ i o = Circ { unCirc :: (LGraph, Cospan i o) } 

-- We need an empty cospan to define the Id on Circ

instance Category Circ where
  type Ok Circ = HasFin
  id = id
  (Circ c) . (Circ c') = undefined
  
-- Let Circ be a symmetric Monoidal Category
-- a morphism in Circ is an isomorphism class X -i> N <o- Y
-- of cospans of finite sets, together with a graph
-- T having N as its set of vertices
