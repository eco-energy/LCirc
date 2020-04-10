{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
module ConCat.Cospan where

import Prelude hiding ((.), id, curry, uncurry, const)
import ConCat.Category
import ConCat.Rep
import ConCat.Misc
import ConCat.Free.VectorSpace

import GHC.Generics (Generic)
import Data.Coerce
import Data.List
import qualified Data.Map as Map
import Data.Map (Map(..))
import ConCat.Circuit
import Data.Bifunctor



{-------------------------
     Operadic Machinery for Cospans with Nat-Indexed Ports
--------------------------}
type PortId = Int


data Port a v = Port { unPort :: (PortId, v) } deriving (Eq, Ord, Show, Generic)
  

portCov :: (a -> a') -> Port a v -> Port a' v
portCov _ = coerce

changePortNum :: forall a a' v. Port a v -> Port a' v
changePortNum = coerce

portSumL :: forall a a' v. Port a v -> Port (a :+ a') v
portSumL = coerce

portSumR :: forall a a' v. Port a' v -> Port (a :+ a') v
portSumR = coerce

portLeft :: forall a a' v. Port a v -> Port (a :+ a') (v :+ v)
portLeft (Port (p, v)) = Port (p, Left v)

portRight :: forall a a' v. Port a' v -> Port (a :+ a') (v :+ v)
portRight (Port (p, v)) = Port (p, Right v)

portLeft' :: forall a a' v. Port a v -> Port (a :+ a') v
portLeft' = portSumL

portRight' :: forall a a' v. Port a' v -> Port (a :+ a') v
portRight' = portSumR


instance HasRep (Port a v) where
  type Rep (Port a v) = (PortId, v)
  abst (p, v) = mkPort p v
  repr (Port (p, v)) = (p, v)


unPortF :: Port a v -> (PortId -> Maybe v)
unPortF (Port (a', v)) = k
  where k a = if a == a' then
          (Just $ const v a') else
          Nothing


unPorts :: Ord v => [Port a v] -> [Port a v]
unPorts ps = sortBy (\a b -> uncurry compare (fst . unPort $ a, fst . unPort $ b) ) ps

listToFn :: [a -> b] -> ([a] -> [b])
listToFn (f:fs) (a:as) = f a:(listToFn fs as)
listToFn [] [] = []

mkPort = curry Port
mkInput = mkPort
mkOutput = mkPort

type Inputs v a = [Port a v]
type Outputs v a = [Port a v]


newtype Cospan k v = Cospan (v `k` v, v `k` v) deriving (Generic)

newtype CospanC v i o = CospanC (Inputs v i, Outputs v o) deriving (Eq, Ord, Show, Generic)


instance (HasRep v) => HasRep (CospanC v i o) where
  type Rep (CospanC v i o) = ([Rep (Port i v)], [Rep (Port o v)])
  abst (i, o) = CospanC (map abst i, map abst o) 
  repr (CospanC (i, o))= (map repr i, map repr o)


mkCospanC :: Inputs v i -> Outputs v o -> CospanC v i o
mkCospanC = curry CospanC


-- A Cospan is a co-product/co-limit
input :: CospanC v i o -> Inputs v i
input (CospanC (i, _)) = i

output :: CospanC v i o -> Outputs v o
output (CospanC (_, o)) = o


compPorts :: forall v i o. (Ord v) => Inputs v i -> Outputs v i -> Map v (v -> v)
compPorts is os = Map.fromList $ map (uncurry unifyPorts) $ zip os is
  where
    unifyPorts :: (Eq v) => Port a v -> Port a v -> (v, (v -> v))
    unifyPorts (Port (p, n)) (Port (p', n')) = (n', (\c -> if c == n' then n else c))


