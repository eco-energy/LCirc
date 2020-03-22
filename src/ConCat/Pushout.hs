{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications#-}
module ConCat.Pushout where
{--
import Prelude hiding (id, (.))

import ConCat.Category

import ConCat.RunCircuit
import ConCat.Circuit

import ConCat.LCirc (LC(..), VI)

import ConCat.KnownNatOps
--import ConCat.Sized
import GHC.TypeLits

type R = Double

{--
type F i o i' o' = (KnownNat i, KnownNat o, KnownNat i', KnownNat o') => [VI] -> [VI] -> CospanT i o i' o'

newtype G c d = G (c -> d -> VI)

instance RepresentableCat F (CospanT)
--}
type CospanT i o i' o' = Template (LC i o) (LC i' o')

f' :: z -> x
f' = undefined

g' :: z -> y
g' = undefined

i1' :: x -> p
i2' :: y -> p

i1' = undefined
i2' = undefined


class (Ok4 k z x y p) => Pushout k z x y p where
  f :: z -> x
  g :: z -> y
  i :: x -> p
  i' :: y -> p


instance Pushout (LC) where
  f = undefined
  g = undefined
  i = undefined
  i' = undefined


--pushout :: forall k z x y p.  Pushout k z x y p  => Coprod k x y -> Either x p
  -- -> ((x, y) -> p)  --forall k z x y p. Pushout k z x y p => z -> Either a b3


{--
pushout
  :: forall k z x y p. (Ok4 k z x y p,
      MonoidalSCat k,
      Pushout k b (k c a) y p,
      Pushout k z t y b,
      Pushout k b x (k d b) p,
      Pushout k z x y z) =>
     (x, y)
     -> k (Coprod k c d) (Coprod k a b)
--}



pushout
  :: forall k z x y p.
  Ok4 k z x y p
  => MonoidalSCat k
  => Pushout k z x y p
  => (x, y)
  -> k (Coprod k x p)
     (Coprod k y p)
pushout = (f . i') +++ (g . i')
--}
