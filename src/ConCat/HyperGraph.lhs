> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE AllowAmbiguousTypes#-}
> {-# LANGUAGE RankNTypes #-}
> {-# LANGUAGE Rank2Types #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE ConstraintKinds #-}
> {-# LANGUAGE PolyKinds #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE TypeApplications #-}
> {-# LANGUAGE ScopedTypeVariables#-}
> module ConCat.HyperGraph where
>
> import Prelude hiding ((.), id, curry, uncurry)
> import ConCat.Category
> import ConCat.Shaped
> import ConCat.Rep
> import ConCat.Circuit hiding (abstC)
> import ConCat.Misc
> import ConCat.KnownNatOps
> import GHC.TypeNats
> import ConCat.AltCat (Finite(..), FiniteCat(..))
> import Control.Newtype.Generics
> import GHC.Generics
> import ConCat.Additive
> import Data.Monoid


A Symmetric Monoidal Category where the morphisms are constrained to be Hypergraphs between nodes.
We ultimately want an autoregressive flow on it conditioned on the universe of nodes.

This is achieved with a Frobenius Structure (X, ux, dx nx ex)

> type SymMonC k = (OkCoprod k, FiniteCat k, MonoidalPCat k, CoproductCat k)

> class (Monoid x) => FrobeniusMonoid x where
>   u :: x :* x -> x
>   n :: () -> x
>
> {--
>   RULES:
>       assoc : (x :* y) :* z == x :* (y :* z)
>       unitality : () :* x == x
>       commutativity : x :* y == y :* x
> --}


> class CommutativeComonoid x where
>   d :: x -> x :* x
>   e :: x -> ()

> {-
>   Rules:
>       coassociativity
>       counitality
>       cocommutativity
> -}

> class (SymMonC k) => FrobeniusStructure k where
>  ux :: n :+ n -> n :+ n -> n :+ n
>  dx :: n :+ n -> n :+ n :* n :+ n
>  nx :: () -> n :+ n
>  ex :: n :+ n -> ()

> {- RULES
>   (X, u, n) is a commutative monoid
>   (X, d, e) is a cocommutative comonoid
>   The Frobenius Law
>      (x :* y) :* (w :* z)
> -}


> type OkFinColim k = (CoterminalCat k)


> {--
> class (Category k) => Cospan k where
>    i :: Ok2 k i v => i -> v
>    o :: Ok2 k o v => o -> v
> --}

> type OkCospan k v = (Ord k) 
> newtype CospanC k v i o = CospanC ((i `k` v) :* (o `k` v))
>
> instance HasRep (CospanC k v i o) where
>   type Rep (CospanC k v i o) = ((i `k` v), (o `k` v))
>   abst f = CospanC f
>   repr (CospanC f) = f

> cospan :: (Category k, Ok3 k v i o) => (i `k` v) :* (o `k` v) -> CospanC k v i o
> cospan f = abst f
> 
> instance FrobeniusStructure (CospanC k v) where
>   ux = undefined
>   dx = undefined
>   nx = undefined
>   ex = undefined


> instance Category (CospanC k v) where
>   --type Ok (CospanC k v) = (OkCospan k)
>   id = id
>   -- (.) :: Cospan v b c -> Cospan v a b -> Cospan v a c
>   (CospanC (i, o)) . (CospanC (i', o')) = undefined
>   --Cospan (Left (Right r)) . (Cospan (Left (Right r'))) = undefined
>   --Cospan (Right r) . Cospan (Right r') = undefined
> 
> instance ProductCat (CospanC k v) where
>   exl = undefined
>   exr = undefined
>   dup = undefined
> 
> instance CoproductCat (CospanC k v) where
>   inl = undefined
>   inr = undefined
>   jam = undefined
> 
> instance BraidedPCat (CospanC k v) where
>   swapP = undefined
> 
> instance MonoidalPCat (CospanC k v) where
>   (CospanC c) *** (CospanC c') = undefined
> 
> instance FiniteCat (CospanC k v) where
>   unFinite = undefined
>   unsafeFinite = undefined



Under the laws:

n1 = id1 = ex1

A Hypergraph category that is also a prop over sets of
Finite Objects

For any C with finite colimits, Cospan C is a hypergraph category.

a colimit in this sense is just two morphisms (f, g) into a set,
i.e a coproduct in the category Set.



