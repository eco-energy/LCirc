{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}


module ConCat.Transformer where

import ConCat.Deep

import ConCat.Free.Affine

import ConCat.Chain

import ConCat.Choice

import ConCat.Continuation

import ConCat.Incremental

import ConCat.Interval

import ConCat.FFT

import ConCat.Free.LinearRow

import ConCat.RAD

import ConCat.Misc

import ConCat.Scan

import Data.Key
import GHC.Generics ((:*:))

-- Let us fold an initial algebra with a neural network.




type PType = ()

--attend :: forall i o s. i s -> o s
attend (h:h':hs) v v' a = (h a *^ v)
{-# INLINE attend #-}


-- what is the loss on attention?



data Nodes p a b = Stochastic p a b | I a | O b | Loss b


--attnGrad :: I (a s -> b s) -> Loss a
attnGrad err xys = errGrad err xys 

type AVec a b = a --* b

