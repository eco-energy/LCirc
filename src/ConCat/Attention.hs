{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveGeneric #-}
module ConCat.Attention where

import ConCat.Misc
import ConCat.Deep
import GHC.Generics
import qualified ConCat.TArr as T
-- use a fixed point functor h
-- with a duplicative structure on h 
--type Multihead h e = h e -> e

--multihead es = norm . add


class HasP i pw o where
  params :: CospanL i pw o
  fold :: i -> pw -> o 
  




newtype CospanL i p o = CospanL (((i -> p -> o) :* p) -> i) deriving (Generic)

class HasDim sh a where
  dim :: a -> sh

type MultiHead p i o = CospanL [i] ((i -> p -> o) -> ([o] -> o)) o
type FFN p s = CospanL s (p -> s -> s) s
type AddNorm p s i o = CospanL i (p -> i -> o) o


--type Attn h aw fw = (HasDim fw h, HasDim aw h) => (AddNorm (a))

--attn :: forall i o heads fw ff2 lin. Embed [i] -> PosEncoding (Embed i) ->  Attn h w


--positionalEncoding :: Embedding w ->


-- All the model sublayers and the embedding layer
-- have outputs of modelDim 512.

--data Layer d f s = Layer (f d, s d)

data Encoder p d = Stack [Encoder p d]
  | Layer (Encoder p d) (Encoder p d) -- A layer is made up of a self attention layer and a 
  | SelfAttention (MultiHead d p d)
  | Norm (AddNorm p (Encoder p d, Encoder p d) (Encoder p d) (Encoder p d))
  | FF p d
  deriving (Generic)
