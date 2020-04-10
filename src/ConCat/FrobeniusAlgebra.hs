{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
module ConCat.FrobeniusAlgebra where

import Prelude hiding (id, (.), uncurry, curry, const)
import qualified Prelude as P

import ConCat.Category
import ConCat.Pair
import ConCat.Rep
import GHC.Generics ((:.:)(..), Generic)
import ConCat.Misc

class (MonoidalSCat k) => Frobenius (k :: * -> * -> *)  where
  join :: (Ok3 k a b c) => a `k` c -> b `k` c -> ((a :* b) `k` c)
  split :: (Ok2 k a b) => (a `k` b) -> (a `k` (b :* b))
  unit :: (Ok k a) => (() `k` a)
  counit :: (Ok k a) => (a `k` ())


{-
Laws:
associativity: join a (join b c) =  join (join a b) c
unitality: unit 
coassociativity: split a 
-}
