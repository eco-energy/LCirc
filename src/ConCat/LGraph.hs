{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
module ConCat.LGraph where

import Prelude hiding ((.), id, curry, uncurry)
import ConCat.Category
import ConCat.Rep
import ConCat.Misc
import ConCat.Pair
import ConCat.Free.VectorSpace
import Data.Bifunctor
import GHC.Generics hiding (Rep, R)
import qualified Data.Set as Set
import Data.Set (Set(..))
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map(..))

type OkLV l v = (Ord v, Ord l, Eq v, Eq l) 

type OkV v = (Ord v, Eq v)

class (OkLV l v) => OkLV' l v i





{-------------------  The Nodes ------------------------}

type NodeId = Int

newtype VI = VI (NodeId, Pair R) deriving (Show, Generic)

instance Eq (VI) where
  (VI (n, a :# b)) == (VI (n', a' :# b')) = n == n' && a == a' && b == b'

instance Ord VI where
  compare (VI (n, a :# b)) (VI (n', a' :# b')) = compare (n, a, b) (n', a', b')

instance HasRep VI where
  type Rep (VI) = (R, R, R)
  repr (VI (a, v :# i)) = (fromIntegral a, v, i)
  abst (a, v, i) = VI (floor a, v :# i)

instance HasV R VI



{----------------------------------------------------------------------------------------
         Labelled Graphs where vertices are finite sets and edges have a label
----------------------------------------------------------------------------------------}


-- A graph is a finite set E of edges and a finite set N of nodes, equipped with a pair of functions
-- s,t: E -> N, assigning to each edge its source and target. e is an edge from s(e) to t(e).
-- An lgraph has an additional function, l: E -> L assigning a label to each edge.

newtype LG l v = LG { runLG :: (Nodes v, Edges l v) } deriving (Eq, Ord, Show, Generic)

instance (HasRep l, HasRep v, OkLV l v) => HasRep (LG l v) where
  type Rep (LG l v) = (Rep (Nodes v), Rep (Edges l v))
  abst (n, e) = LG (abst n, abst e)
  repr (LG (n, e)) = (repr n, repr e)


newtype Edges l v = Edges { getEdges :: Set (Edge l v) } deriving (Eq, Ord, Show, Generic)


instance (HasRep l, HasRep v, OkLV l v) => HasRep (Edges l v) where
  type Rep (Edges l v) = [Edge l v]
  abst = Edges . Set.fromList
  repr = Set.toList . getEdges

newtype Nodes v = Nodes (Set v) deriving (Eq, Ord, Show, Generic)

instance (Ord v, HasRep v) => HasRep (Nodes v) where
  type Rep (Nodes v) = [Rep v]
  abst = Nodes . Set.fromList . (map abst)
  repr (Nodes n) = (map repr) . Set.toList $ n

nodes :: LG l v -> Nodes v
nodes = fst . runLG

edges :: LG l v -> Edges l v
edges = snd . runLG

mkLG :: Nodes v -> Edges l v -> LG l v
mkLG = curry LG

mkLG' ns es = mkLG (mkNodes ns) $ mkEdges es

mkNodes :: (Ord v) => [v] -> Nodes v
mkNodes = Nodes . Set.fromList

mkEdges :: (Ord v, Ord l) => [Edge l v] -> Edges l v
mkEdges = Edges . Set.fromList


newtype Edge l v = Edge (Pair v, l) deriving (Show, Generic)


instance (HasRep l, HasRep v) => HasRep (Edge l v) where
  type Rep (Edge l v) = (v, v, l)
  abst (s, t, l) = Edge (s :# t, l) 
  repr (Edge (s :# t, l)) = (s, t, l)

instance (HasRep l, HasRep v, HasV R l, HasV R v) => HasV R (Edge l v)

instance Bifunctor Edge where
  bimap f g (Edge (s :# t, l)) = Edge (((g s) :# (g t)), f l)

--instance Bifunctor Edges where
--  bimap f g (Edges e) = Edges $ Set.map (bimap f g) e


mkEdge :: v -> v -> l -> Edge l v
mkEdge s t l = Edge (s :# t, l)

-- The direction of an edge is irrelevant to its equivalence relation with another edge, hence
-- the bidirectional check for matching nodes.
instance (Eq l, Eq v) => Eq (Edge l v) where
  (Edge (a :# b, l)) == (Edge (a' :# b', l')) = (a == a' && b == b' || a == b' && b == a') && l == l'

-- Simple lexicographical order serves our intent when putting edges into maps and sets
instance (Ord l, Ord v) => Ord (Edge l v) where
  (Edge (a :# b, l)) <= (Edge (a' :# b', l')) = (a, b, l) <= (a', b', l')

src :: Edge l v -> v
src (Edge (s :# _, _)) = s

tgt :: Edge l v -> v
tgt (Edge (_ :# t, _)) = t

label :: Edge l v -> l
label (Edge (_, l)) = l

type Labels l = Set l

labels :: (Ord l, Ord v) => Edges l v -> Labels l
labels (Edges es) = Set.map label es




{------------------ Composition -----------------------------}


compNodes :: (OkV v) => Nodes v -> Nodes v -> Map v (v -> v) -> Nodes v
compNodes (Nodes n) (Nodes n') chngs = Nodes $ Set.union n n'_
  where
    n'_ = foldl (\k nn-> Set.delete nn k) n' (Map.keys chngs)

compEdges :: (OkLV l v) => Edges l v -> Edges l v -> Map v (v -> v) -> Edges l v
compEdges (Edges e1) (Edges e2) e12 = Edges $ Set.union e1 e2'
  where
    e2' = Set.map re e2
    re e = replaceMatching (Map.lookup (src e) e12) (Map.lookup (tgt e) e12) e


replaceMatching :: forall v l. Maybe (v -> v) -> Maybe (v -> v) -> Edge l v ->  Edge l v
replaceMatching (Just f) (Just g) e@(Edge (s :# t, l)) = (Edge (f s :# g t, l))
replaceMatching (Just f) Nothing e@(Edge (s :# t, l)) = (Edge (f s :# t, l))
replaceMatching Nothing (Just g) e@(Edge (s :# t, l)) = (Edge (s :# g t, l))
replaceMatching Nothing Nothing e@(Edge (s :# t, l)) = e

