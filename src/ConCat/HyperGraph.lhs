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


A Symmetric Monoidal Category where the morphisms are constrained to be Hypergraphs between nodes.
We ultimately want an autoregressive flow on it conditioned on the universe of nodes.

This is achieved with a Frobenius Structure (X, ux, dx nx ex)

> type SymMonC k = (OkCoprod k, FiniteCat k, MonoidalPCat k, CoproductCat k)

> class (SymMonC k) => FrobeniusStructure k where
>  ux :: n :+ n -> n :+ n -> n :+ n
>  dx :: n :+ n -> n :+ n :* n :+ n
>  -- nx :: () -> (() -> n :+ n)
>  nx :: () -> n :+ n
>  ex :: n :+ n -> ()

> newtype CospanC v i o = CospanC
>   { unCSpan :: (i :+ v) :+ o }


> type F n = (Finite n)
> instance Category (CospanC v) where
>   id = id
>   -- (.) :: CospanC v b c -> CospanC v a b -> CospanC v a c
>   CospanC (Left (Left r)) . (CospanC (Left (Left r'))) = undefined
>   CospanC (Left (Right r)) . (CospanC (Left (Right r'))) = undefined
>   CospanC (Right r) . CospanC (Right r') = undefined
> 
> instance ProductCat (CospanC v) where
>   exl = undefined
>   exr = undefined
>   dup = undefined
> 
> instance CoproductCat (CospanC v) where
>   inl = undefined
>   inr = undefined
>   jam = undefined
> 
> instance BraidedPCat (CospanC v) where
>   swapP = undefined
> 
> instance MonoidalPCat (CospanC v) where
>   (CospanC c) *** (CospanC c') = undefined
> 
> instance FiniteCat (CospanC v) where
>   unFinite = undefined
>   unsafeFinite = undefined


> instance FrobeniusStructure (CospanC n) where
>   ux = undefined
>   dx = undefined
>   nx = undefined
>   ex = undefined
>   --ux (CospanC (Right n)) = n
>   --ux (CospanC (Left n)) = n


Under the laws:

n1 = id1 = ex1

A Hypergraph category that is also a prop over sets of
Finite Objects

For any C with finite colimits, Cospan C is a hypergraph category.

a colimit in this sense is just two morphisms (f, g) into a set,
i.e a coproduct in the category Set.



