{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}
module ConCat.LCirc where

import ConCat.Category
import GHC.Generics (Generic)

-- A category where the morphisms are circuits made of wires with circuit elemtns on them



-- A graph is a finite set E of edges and a finite set N of nodes equipped with a pair of functions s,t: E -> N,
-- assigning to each edge its source and target. e is an edge from s(e) to t(e). An lgraph has an additional function
-- l: E -> L assigning a label to each edge.


type R = Double

data LGraph l e n = LGraph
  { s :: e -> n
  , t :: e -> n
  , l :: e -> l
  } deriving (Generic)


type ResGraph e n = LGraph R e n



data LCircuit l e n = LCircuit
  { cospan :: (n -> n, n ->  n)
  , lgraph :: LGraph l e n
  } deriving (Generic)

