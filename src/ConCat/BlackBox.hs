{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

module ConCat.BlackBox where

import ConCat.Category
import ConCat.Misc
import ConCat.LCirc


data GenCirc f where
  Join :: GenCirc f -> GenCirc f -> GenCirc f
  Dup :: GenCirc f -> GenCirc (f :* f)
  Unit :: () -> GenCirc f
  Counit :: GenCirc f -> GenCirc ()


--blackbox :: (OkLV l v) GenCirc (LCirc') -> 
--blackbox 
