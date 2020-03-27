{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
module ConCat.LCirc where

import Prelude hiding (id, (.), uncurry, curry, const)
import qualified Prelude as P

import ConCat.Category
--import ConCat.
import ConCat.Pair
import ConCat.Rep
import GHC.Generics (Generic)
import Data.Finite
import GHC.TypeLits
import qualified Data.Set as Set
import Data.Set (Set(..))
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map(..))
import ConCat.Circuit
import Data.List
import Data.Maybe
import ConCat.Misc ((:*), (:+))
import Data.Bifunctor hiding (first, second)
import ConCat.ADFun

-- A category where the morphisms are circuits made of wires with circuit elemtns on them

type NodeId = Int

type VI = VI' NodeId R

newtype VI' i r = VI (i, Pair r) deriving (Show, Generic)

mkVI :: NodeId -> VI
mkVI i = VI (i, 0 :# (0 :: Double))

tag :: VI -> NodeId
tag (VI (n, _)) = n

instance (Eq i, Eq r) => Eq (VI' i r) where
  (VI (p, a :# b)) == (VI (p', a' :# b')) = p == p' && a == a' && b == b'

instance (Ord i, Ord r) => Ord (VI' i r) where
  compare (VI (p, a :# b)) (VI (p', a' :# b')) = compare (a, b) (a', b')

instance (HasRep i, HasRep r) => HasRep (VI' i r) where
  type Rep (VI' i r) = (i, r, r)
  repr (VI (p, a :# b)) = (p, a, b)
  abst (p, v, i) = VI (p, v :# i)


instance Bifunctor (VI') where
  bimap f g (VI (idx, v :# i)) = VI (f idx, g v :# g i)


{----------------------------------------------------------------------------------------
         Labelled Graphs where vertices are finite sets and edges have a label
----------------------------------------------------------------------------------------}
type R = Double


-- A graph is a finite set E of edges and a finite set N of nodes, equipped with a pair of functions
-- s,t: E -> N, assigning to each edge its source and target. e is an edge from s(e) to t(e).
-- An lgraph has an additional function, l: E -> L assigning a label to each edge.

newtype LG l v = LG { runLG :: (Nodes v, Edges l v) } deriving (Eq, Ord, Show, Generic)

instance Bifunctor LG where
  bimap f g (LG (ns, es)) = LG (fmap g ns, (bimap f g es))

instance (HasRep l, HasRep v) => HasRep (LG l v) where
  type Rep (LG l v) = LG l v
  abst = id
  repr = id


newtype Edges l v = Edges { getEdges :: [Edge l v] } deriving (Eq, Ord, Show, Generic)

instance Bifunctor Edges where
  bimap f g (Edges es) = Edges $ map (bimap f g) es 


toEdgeSet :: (OkLV l v) => Edges l v -> Set (Edge l v)
toEdgeSet = Set.fromList . getEdges

fromEdgeSet :: (OkLV l v) => Set (Edge l v) -> Edges l v
fromEdgeSet = Edges . Set.toList


instance (HasRep l, HasRep v) => HasRep (Edges l v) where
  type Rep (Edges l v) = Edges l v
  abst = id
  repr = id


newtype Nodes v = Nodes [v] deriving (Functor, Generic, Eq, Ord, Show)


fromNodeSet :: (OkV v) => Set v -> Nodes v
fromNodeSet = Nodes . Set.toList

toNodeSet :: (OkV v) => Nodes v -> Set v
toNodeSet (Nodes vs) = Set.fromList vs

nodes :: LG l v -> Nodes v
nodes = fst . runLG

edges :: LG l v -> Edges l v
edges = snd . runLG

mkLG :: Nodes v -> Edges l v -> LG l v
mkLG = curry LG

mkLG' ns es = mkLG (mkNodes ns) $ mkEdges es

mkNodes :: (Ord v) => [v] -> Nodes v
mkNodes = Nodes

mkEdges :: (Ord v, Ord l) => [Edge l v] -> Edges l v
mkEdges = Edges


newtype Edge l v = Edge (Pair v, l) deriving (Show, Generic)

instance Bifunctor Edge where
  bimap f g (Edge (s :# t, l)) = Edge (((g s) :# (g t)), f l)

instance (HasRep l, HasRep v) => HasRep (Edge l v) where
  type Rep (Edge l v) = (v, v, l)
  abst (s, t, l) = Edge (s :# t, l) 
  repr (Edge (s :# t, l)) = (s, t, l)


mkEdge :: v -> v -> l -> Edge l v
mkEdge s t l = Edge (s :# t, l)

-- The direction of an edge is irrelevant to its equivalence relation with another edge, hence
-- the bidirectional check for matching nodes.
instance (Eq l, Eq v) => Eq (Edge l v) where
  (Edge (a :# b, l)) == (Edge (a' :# b', l')) = (a == a' && b == b' || a == b' && b == a') && l == l'

-- Simple lexicographical order serves our intent when putting edges into maps and sets
instance (Ord l, Ord v) => Ord (Edge l v) where
  (Edge (a :# b, l)) <= (Edge (a' :# b', l')) = (a, b, l) <= (a', b', l')

srcId :: Edge CircEl VI -> NodeId
srcId = tag . src 

tgtId :: Edge CircEl VI -> NodeId
tgtId = tag . tgt

src :: Edge l v -> v
src (Edge (s :# _, _)) = s

tgt :: Edge l v -> v
tgt (Edge (_ :# t, _)) = t

label :: Edge l v -> l
label (Edge (_, l)) = l

type Labels l = [l]

labels :: (Ord l, Ord v) => Edges l v -> Labels l
labels (Edges es) = map label es


{-------------------------
     Operadic Machinery for Cospans with Nat-Indexed Ports
--------------------------}


type PortId = Int

data Port a v = Port { unPort :: (PortId, v) } deriving (Eq, Ord, Show, Generic)

instance Functor (Port a) where
  fmap f (Port (p, v)) = Port (p, f v)

instance HasRep (Port a v) where
  type Rep (Port a v) = (PortId, v)
  abst (p, v) = Port (p, v)
  repr (Port (p, v)) = (p, v)


unPortF :: Port a v -> (PortId -> Maybe v)
unPortF (Port (a', v)) = k
  where k a = if a == a' then
          (Just $ const v a') else
          Nothing


unPorts :: Ord v => [Port a v] -> [Port a v]
unPorts ps = sortBy (\a b -> uncurry compare (fst . unPort $ a, fst . unPort $ b) ) ps


mkPort :: PortId -> VI -> Port i VI
mkPort = curry Port

mkInput :: PortId -> VI -> Port i VI
mkInput = mkPort

mkOutput :: PortId -> VI -> Port o VI
mkOutput = mkPort

type Inputs v a = [Port a v]
type Outputs v a = [Port a v]


-- :- is the LCirc morphism where Ob(C a) = n_, a where n <= Finite n'
-- along with a Representable Functor over Ob(LCirc)

--data a :- b = C { unC :: KleisliM LCirc Source a Target a }


{--
cospan :: i -> o -> z -> ((i :- z), (o :- z))
cospan = undefined

mkSpider plan = sow :- plan
  where
    sow (Id a,  Id b) = foldlWithKey

instance Category (:-) where
  id = uncurry . Id
--}


newtype Cospan k v = Cospan (v `k` v, v `k` v) deriving (Generic)

newtype CospanC v i o = CospanC { unCspanC :: ([Port i v], [Port o v]) } deriving (Eq, Ord, Show, Generic)

instance HasRep (CospanC v i o) where
   type Rep (CospanC v i o) = CospanC v i o
   abst = id
   repr = id


mkCospanC :: Inputs v i -> Outputs v o -> CospanC v i o
mkCospanC = curry CospanC


-- A Cospan is a co-product/co-limit
input :: CospanC v i o -> Inputs v i
input (CospanC (i, _)) = i

output :: CospanC v i o -> Outputs v o
output (CospanC (_, o)) = o


{---------------------------------------------------------------------------------
    An LCirc is a Pair of an LGraph over a label-set of Circuit Elements
    and a Cospan over the category of Finite Sets.
    Equality for LCirc is defined over an isomorphism class,
    where the names of the nodes of LGraph can be transformed by any mapping (v -> v)
    without affecting the equality of two LCircs.
---------------------------------------------------------------------------------}

data CircEl = Res R | Cap R | Ind R deriving (Eq, Ord, Show, Generic)

instance HasRep CircEl where
  type Rep (CircEl) = (Int, R) 
  repr (Res r) = (1, r)
  repr (Cap c) = (2, c)
  repr (Ind i) = (3, i)
  abst (1, el) = Res el
  abst (2, el) = Cap el
  abst (3, el) = Ind el

    
newtype LCirc l v i o = LCirc { runLCirc :: (LG l v, CospanC v i o) } deriving (Eq, Ord, Show, Generic)

newtype LCirc' i o = LCirc' (LCirc CircEl VI i o) deriving (Eq, Ord, Show, Generic)

  
instance (HasRep l, HasRep v) => HasRep (LCirc l v i o) where
  type Rep (LCirc l v i o) = (LG l v, CospanC v i o)
  abst = LCirc
  repr (LCirc a) = a

instance HasRep (LCirc' i o) where
  type Rep (LCirc' i o) = (LG CircEl VI, CospanC VI i o)
  abst =  LCirc' . LCirc
  repr (LCirc' (LCirc a)) = a

instance Category LCirc' where
  type Ok (LCirc') = (Ord)
  id = id
  -- (.) :: forall b c a. Ok3 (LCirc) 
  l . l' = (flip composeLC) l l'

instance ProductCat LCirc' where
  exl = exl
  exr = exr
  dup = dup

instance AssociativePCat LCirc' where
  lassocP = lassocP
  rassocP = rassocP

instance BraidedPCat LCirc' where
  swapP = swapP

instance MonoidalPCat LCirc' where
  f ***  g = f *** g
  first = first
  second = second

instance AssociativeSCat LCirc' where
  lassocS = lassocS
  rassocS = rassocS

instance BraidedSCat LCirc' where
  swapS = swapS

instance MonoidalSCat LCirc' where
  f +++ g = f +++ g
  left = left
  right = right


instance CoproductCat LCirc' where
  inl = inl
  inr = inr
  jam = jam


-- For LCirc equality testing, in order to form a category we must have associativety
-- this can only be obtained right now if the equivalence relation between two LCircs counts
-- an isomorphism that is a vertex bijection which is both edge-preserving and label-preserving as equality.
-- Because otherwise the names of the labels end up being muddled up.
-- Semantically, we're working over isomorphism classes of cospans anyways.
-- instance forall l v i o. (Eq l, Eq v, Ord l, Ord v) => Eq (LCirc l v i o) where
--  (LCirc (lg, cs)) == (LCirc (lg', cs')) = iso (toLG' lg) (toLG' lg')
    -- If we defined such a bijection then we can just apply it to all the vertices, all the edges and all the cospans.
    -- If the equivalence relation holds after the bijection, then the graphs are equivalent.
    -- The reason we can

{--
instance (Show l, Show v) => Show (LCirc l v i o) where
  show (LCirc (lg, CospanC (i, o))) = "LCirc: " <> (show lg)

instance (Eq l, Eq v) => Eq (LCirc l v i o) where
  (LCirc (lg, CospanC (i, o))) == (LCirc (lg', CospanC (i', o'))) = lg == lg'
    && i == i'
    && o' == o'
--}
mkLC = curry LCirc

mkLC' :: forall i o. LG CircEl VI -> CospanC VI i o -> LCirc' i o 
mkLC' lg cs = LCirc' $ LCirc (lg, cs)

{------------      Serial Composition of Cospans       --------------------------}

-- This should obey the category laws

type OkLV l v = (Ord v, Ord l, Eq v, Eq l) 

type OkV v = (Ord v, Eq v)

composeLC :: forall i o o'.  LCirc' i o -> LCirc' o o' -> LCirc' i o'
composeLC (LCirc' (LCirc (LG (n, e), CospanC (i, o))))
           (LCirc' (LCirc (LG (n', e'), CospanC (i', o')))) = mkLC' lg'' cspan''
  where
    replacements = compPorts i' o
    lg'' = LG (compNodes n n' replacements, compEdges e e' replacements)
    o'' = map quotient o'
    cspan'' = CospanC (i, o'')
    quotient (Port(pid, vi@(VI (nid, _)))) = case Map.lookup nid replacements of
                  Just f -> Port (pid, f vi)
                  Nothing -> Port (pid, vi)
              

compNodes :: Nodes VI -> Nodes VI -> Map NodeId (VI -> VI) -> Nodes VI
compNodes (Nodes []) (Nodes []) _ = Nodes []
compNodes (Nodes a) (Nodes []) _ = Nodes a
compNodes n (Nodes n') chngs = fromNodeSet $ Set.union (toNodeSet n) n'_
  where
    n'_ =  Set.fromList $ map apl n'
    apl v@(VI(i, vi)) = case Map.lookup i chngs of
                Nothing -> v
                Just f -> f v
    

compEdges :: Edges CircEl VI -> Edges CircEl VI -> Map NodeId (VI -> VI) -> Edges CircEl VI
compEdges e1 e2 e12 = fromEdgeSet $ Set.union (toEdgeSet e1) e2'
  where
    e2' = Set.map re (toEdgeSet e2)
    re e = replaceMatching (Map.lookup (srcId e) e12) (Map.lookup (tgtId e) e12) e
    replaceMatching :: Maybe (VI -> VI) -> Maybe (VI -> VI)
                    -> Edge CircEl VI ->  Edge CircEl VI
    replaceMatching (Just f) (Just g) e@(Edge (s :# t, l)) = (Edge (f s :# g t, l))
    replaceMatching (Just f) Nothing e@(Edge (s :# t, l)) = (Edge (f s :# t, l))
    replaceMatching Nothing (Just g) e@(Edge (s :# t, l)) = (Edge (s :# g t, l))
    replaceMatching Nothing Nothing e@(Edge (s :# t, l)) = e



compPorts :: forall i o.  Inputs VI i -> Outputs VI i -> Map NodeId (VI -> VI)
compPorts [] [] = Map.empty
compPorts is [] = Map.empty
compPorts is os = Map.fromList $ map (uncurry unifyPorts) $ zip os is
  where
    unifyPorts :: Port a VI -> Port a VI -> (NodeId, (VI -> VI))
    unifyPorts (Port (p, (VI (n, vi)))) (Port (p', (VI (n', vi')))) =
      (n', (\(VI (c, vi)) -> if c == n' then (VI (n, vi)) else (VI (c, vi))))


toCardinal :: LCirc' i o -> LCirc' i o
toCardinal (LCirc' (LCirc (lg, cs))) = undefined
  where
    es' = bimap id safeLookupVI es
    ns' = fmap (bimap safeLookup id) ns
    is' = map (fmap safeLookupVI) is
    os' = map (fmap safeLookupVI) os
    (LG (Nodes ns, es)) = lg
    (CospanC (is, os)) = cs
    r :: Map NodeId NodeId
    r = Map.fromList $ zip (map tag ns) [0 :: NodeId, 1..]
    safeLookupP :: Port i VI -> Port i VI
    safeLookupP (Port (p, n)) = Port (p, safeLookupVI n) 
    safeLookupVI :: VI -> VI
    safeLookupVI vi@(VI (i, v)) = VI (safeLookup i, v)
    safeLookup :: NodeId -> NodeId
    safeLookup i = case n of
      Nothing -> i
      Just n' -> n'
      where n = Map.lookup i r



{----------------------------------------------------------------------------------------
         Category Instances
-----------------------------------------------------------------------------------------}


-- Given a category C, a cospan in C is a diagram of the form
-- X -f> N <g- Y
-- This is a mapping in to the set of nodes in some network where f and g pick out the inputs and outputs.


-- Monoidal Category

-- the tensor product: <> :: C x C -> C
-- the unit object I in Ob(C)
-- associator, a natural transformation : (x <> y) <> z -> x <> (y <> z)
-- the left unitor : I <> x -> x
-- the right unitor : x <> I -> x

-- A monoidal category is Strict if the associator, the left unutir and the right unitor are identities

-- Tensoring allows setting objects side by side and also morphisms side by side with each other.

-- Braided Monoidal Category
-- B_xy : x <> y -> y <> x
-- Symmetric if B_yx . B_xy = id(x<>y)


{--
instance HasRep (LCirc l v i o) where
  type Rep (LCirc l v i o) = (l, v)
  abst = undefined
  repr = undefined


instance Category LCirc where
  type Ok LCirc = Ord
  id = id
  (LCirc (lg, Cospan (i, o))) . (LCirc (lg', Cospan (i', o'))) = LCirc $ undefined


--}

{----------------------------------------------------------------------------------------
         Circuit Elements
----------------------------------------------------------------------------------------}



{-----------------------------------------------------------------------------------------
         Graph Isomorphism
------------------------------------------------------------------------------------------

data Adjacency a = Adj [(a, [a])]

data LG' l v = LG' [v] [Edge l v]


toLG' :: LG l v -> LG' l v
toLG' (LG (ns, (Edges es))) = LG' (Set.toAscList ns) (Set.toAscList es)

isoLG :: (Ord l, Ord v) => LG l v -> LG l v -> Bool
isoLG l l' = iso (toLG' l) (toLG' l')

iso :: (Ord l, Ord v) => LG' l v -> LG' l v -> Bool
iso g@(LG' xs ys) h@(LG' xs' ys') = length xs == length xs' &&
                                        (labels . Edges . Set.fromList $ ys) == (labels . Edges . Set.fromList $ ys') &&
                                        canon g == canon h
  where
  canon :: (Ord l, Enum v, Eq v) => LG' l v -> String
  canon g = minimum $ map f $ perm $ length a
     where
        Adj a = graphToAdj g
        v = map fst a
        perm n = foldr (\x xs -> [i : s | i <- [1..n], s <- xs, i `notElem` s]) [[]] [1..n]
        f p = let n = zip v p
              in show [(snd x,
                        sort id $ map (\x ->
                           snd $ head $ snd $ break ((==) x . fst) n) $ snd $ find a x)
                      | x <- sort snd n]
        sort f n = foldr (\x xs -> let (lt, gt) = break ((<) (f x) . f) xs
                                   in lt ++ [x] ++ gt) [] n
        find a x = let (xs, ys) = break ((==) (fst x) . fst) a in head ys
        graphToAdj :: (Eq v) => LG' l v -> Adjacency v
        graphToAdj (LG' [] _)      = Adj []
        graphToAdj (LG' (x:xs) ys) = Adj ((x, ys' >>= f) : zs)
          where
            ys' = map (\(Edge (s :# t, l))-> (s, t)) ys
            f (a, b)
              | a == x = [b]
              | b == x = [a]
              | otherwise = []
            Adj zs = graphToAdj (LG' xs ys)

--}
-- A network, such as an electrical circuit, with m inputs and n outputs is a morphism from m to n,
-- while putting networks together in series is composition, and setting them side by side is tensoring.

-- Each kind of network corresponds to a mathematically natural prop.
