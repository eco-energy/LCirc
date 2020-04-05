{-# LANGUAGE FlexibleInstances #-}
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
{-# LANGUAGE ScopedTypeVariables #-}
module ConCat.LCirc where

import Prelude hiding (id, (.), uncurry, curry, const)
import qualified Prelude as P

import ConCat.Category
--import ConCat.
import ConCat.Pair
import ConCat.Rep
import GHC.Generics (Generic)
import Data.Bifunctor
import Data.Finite
import GHC.TypeLits
import qualified Data.Set as Set
import Data.Set (Set(..))
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map(..))
import ConCat.Circuit
import Data.List
import Data.Maybe
import ConCat.Misc
import qualified Data.Either as E
import Data.Coerce

-- A category where the morphisms are circuits made of wires with circuit elemtns on them

newtype VI = VI (Pair R) deriving (Show, Generic)

instance Eq (VI) where
  (VI (a :# b)) == (VI (a' :# b')) = a == a' && b == b'

instance Ord VI where
  compare (VI (a :# b)) (VI (a' :# b')) = compare (a, b) (a', b')

instance HasRep VI where
  type Rep (VI) = R :* R
  repr (VI a) = repr a
  abst (v, i) = VI (v :# i)

type LC = LCirc RLC VI



{----------------------------------------------------------------------------------------
         Labelled Graphs where vertices are finite sets and edges have a label
----------------------------------------------------------------------------------------}


-- A graph is a finite set E of edges and a finite set N of nodes, equipped with a pair of functions
-- s,t: E -> N, assigning to each edge its source and target. e is an edge from s(e) to t(e).
-- An lgraph has an additional function, l: E -> L assigning a label to each edge.

newtype LG l v = LG { runLG :: (Nodes v, Edges l v) } deriving (Eq, Ord, Show, Generic)

instance (HasRep l, HasRep v) => HasRep (LG l v) where
  type Rep (LG l v) = LG l v
  abst = id
  repr = id


newtype Edges l v = Edges { getEdges :: Set (Edge l v) } deriving (Eq, Ord, Show, Generic)


newtype Coproduct f g a = Coproduct { getCoproduct :: Either (f a) (g a) } deriving (Eq, Ord, Read, Show, Generic)

left :: f a -> Coproduct f g a
left = Coproduct . Left

right :: g a -> Coproduct f g a
right = Coproduct . Right

coproduct :: (f a -> b) -> (g a -> b) -> Coproduct f g a -> b
coproduct f g = either f g . getCoproduct

tensorEdges :: Edges l v -> Edges l' v' -> Either (Edges l v) (Edges l' v')
tensorEdges e1 e2 = (Left e1)

instance (HasRep l, HasRep v) => HasRep (Edges l v) where
  type Rep (Edges l v) = Edges l v
  abst = id
  repr = id


newtype Nodes v = Nodes (Set v) deriving (Eq, Ord, Show, Generic)


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


{-------------------------
     Operadic Machinery for Cospans with Nat-Indexed Ports
--------------------------}


type PortId = Int
type NodeId = Int

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

data RLC = Res R | Cap R | Ind R deriving (Eq, Ord, Show, Generic)

instance HasRep RLC where
  type Rep (RLC) = (Int, R) 
  repr (Res r) = (1, r)
  repr (Cap c) = (2, c)
  repr (Ind i) = (3, i)
  abst (1, el) = Res el
  abst (2, el) = Cap el
  abst (3, el) = Ind el

    
newtype LCirc l v i o = LCirc { runLCirc :: (LG l v, CospanC v i o) } deriving (Eq, Ord, Show, Generic)

newtype LCirc' i o = LCirc' (LCirc RLC VI i o) deriving (Eq, Ord, Show, Generic)


instance (HasRep l, HasRep v) => HasRep (LCirc l v i o) where
  type Rep (LCirc l v i o) = LCirc l v i o
  abst = id
  repr = id




instance (OkLV l v) => Category (LCirc l v) where
  id = id
  -- (.) :: forall b c a. Ok3 (LCirc) 
  l . l' = (flip composeLC) l l'

instance (OkLV l v) => MonoidalSCat (LCirc l v) where
  lc +++ lc' = tensorLC' lc lc'

instance (Ord l, Ord v) => CoproductCat (LCirc l v) where
  -- inl :: Ok2 k a b => 
  -- inr :: Ok2 k a b => (LCirc l v) b (Coprod k a b)
  -- jam :: Ok k a => a :+ (LCirc l v a a)
  inl = lcirc inl 
  inr = lcirc inr
  jam = lcirc jam

  

instance Bifunctor (LCirc l v) where
  bimap f g (LCirc (lg, CospanC (i, o))) = LCirc (lg,
                                                  CospanC (map (portCov f) i,
                                                           map (portCov g) o))

lcirc :: (a -> b) -> (LCirc l v) a b
lcirc f = mkLC (mkLG (Nodes Set.empty) (Edges Set.empty)) $ mkCospanC [] []


instance (Ord l, Ord v) => BraidedSCat (LCirc l v)

--instance (Ord l, Ord v) => MonoidalPCat (LCirc l v) where
  -- (***) :: LCirc' a c -> LCirc' b d -> LCirc' (LCirc' a b) (Prod LCirc' c d) 
--  (LCirc (lg, cs)) *** (LCirc (lg', cs')) = _


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

mkLC' :: forall i o. LG RLC VI -> CospanC VI i o -> LCirc' i o 
mkLC' lg cs = LCirc' $ LCirc (lg, cs)

{------------      Serial Composition of LCirc Cospans    --------------------------}

-- This should obey the category laws

type OkLV l v = (Ord v, Ord l, Eq v, Eq l) 

type OkV v = (Ord v, Eq v)

class (OkLV l v) => OkLV' l v i


composeLC :: forall l v i o o'.  (OkLV l v) => LCirc l v i o -> LCirc l v o o' -> LCirc l v i o'
composeLC (LCirc (LG (n, e), CospanC (i, o)))
           (LCirc (LG (n', e'), CospanC (i', o'))) = mkLC lg'' cspan''
  where
    replacements = compPorts i' o
    lg'' = LG (compNodes n n' replacements, compEdges e e' replacements)
    o'' = map (\(Port (pid, nid)) -> case Map.lookup nid replacements of
                  Just nid' -> Port (pid, nid' nid)
                  Nothing -> Port (pid, nid)
              ) o'
    cspan'' = CospanC (i, o'')


compNodes :: (OkV v) => Nodes v -> Nodes v -> Map v (v -> v) -> Nodes v
compNodes (Nodes n) (Nodes n') chngs = Nodes $ Set.union n n'_
  where
    n'_ = foldl (\k nn-> Set.delete nn k) n' (Map.keys chngs)

compEdges :: (OkLV l v) => Edges l v -> Edges l v -> Map v (v -> v) -> Edges l v
compEdges (Edges e1) (Edges e2) e12 = Edges $ Set.union e1 e2'
  where
    e2' = Set.map re e2
    re e = replaceMatching (Map.lookup (src e) e12) (Map.lookup (tgt e) e12) e

compPorts :: forall v i o. (OkV v) => Inputs v i -> Outputs v i -> Map v (v -> v)
compPorts is os = Map.fromList $ map (uncurry unifyPorts) $ zip os is
  where
    unifyPorts :: (Eq v) => Port a v -> Port a v -> (v, (v -> v))
    unifyPorts (Port (p, n)) (Port (p', n')) = (n', (\c -> if c == n' then n else c))


replaceMatching :: forall v l. Maybe (v -> v) -> Maybe (v -> v) -> Edge l v ->  Edge l v
replaceMatching (Just f) (Just g) e@(Edge (s :# t, l)) = (Edge (f s :# g t, l))
replaceMatching (Just f) Nothing e@(Edge (s :# t, l)) = (Edge (f s :# t, l))
replaceMatching Nothing (Just g) e@(Edge (s :# t, l)) = (Edge (s :# g t, l))
replaceMatching Nothing Nothing e@(Edge (s :# t, l)) = e



{----------------- Tensor Product for Cospans of LCirc --------------------------------}

-- :: i `k` o -> i' `k` o' -> (i :+ i') `k` (o :+ o')
tensorLC :: forall l v i o i' o'. (OkLV l v) => LCirc l v i o -> LCirc l v i' o' -> LCirc (l :+ l) (v :+ v) (i :+ i') (o :+ o')
tensorLC (LCirc (LG (n, e), CospanC (i, o))) (LCirc (LG(n', e'), CospanC (i', o'))) = LCirc (lg'', CospanC (i'', o''))
  where
    n'' :: Set (v :+ v)
    n'' = Set.union (nodesLeft n) (nodesRight n')
    e'' = Set.union (edgesLeft e) (edgesRight e')
    lg'' = LG (Nodes n'', Edges e'')
    i'' :: Inputs (v :+ v) (i :+ i')
    i'' = (map (portLeft @i @i') i) ++ (map (portRight @i @i') i') 
    o'' :: Outputs (v :+ v) (o :+ o')
    o'' = (map (portLeft @o @o') o) ++ (map (portRight @o @o') o')
    nodesLeft (Nodes ns) = Set.map (Left) ns
    nodesRight (Nodes ns) = Set.map Right ns
    edgesLeft (Edges es) = Set.map (bimap Left Left) es
    edgesRight (Edges es) = Set.map (bimap Right Right) es

tensorLC' :: forall l v i o i' o'. (OkLV l v) => LCirc l v i o -> LCirc l v i' o' -> LCirc l v (i :+ i') (o :+ o')
tensorLC' (LCirc (LG (Nodes n, Edges e), CospanC (i, o))) (LCirc (LG(Nodes n', Edges e'), CospanC (i', o'))) = LCirc (lg'', CospanC (i'', o''))
  where
    n'' = Set.union (n) (n')
    e'' = Set.union (e) (e')
    lg'' = LG (Nodes n'', Edges e'')
    i'' :: Inputs (v) (i :+ i')
    i'' = (map (portLeft' @i @i') i) ++ (map (portRight' @i @i') i') 
    o'' :: Outputs (v) (o :+ o')
    o'' = (map (portLeft' @o @o') o) ++ (map (portRight' @o @o') o')
    nodesLeft (Nodes ns) = Set.map (Left) ns
    nodesRight (Nodes ns) = Set.map Right ns
    edgesLeft (Edges es) = Set.map (bimap Left Left) es
    edgesRight (Edges es) = Set.map (bimap Right Right) es
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

instance AssociativePCat LCirc where
  lassocP = undefined
  rassocP = undefined

instance BraidedPCat LCirc where
  swapP = undefined

instance MonoidalPCat LCirc where
  LCirc f *** LCirc g = LCirc $ undefined
  first (LCirc f) = LCirc $ undefined
  second (LCirc g) = LCirc $ undefined

instance ProductCat LCirc where
  exl = undefined
  exr = undefined
  dup = undefined

instance AssociativeSCat LCirc where
  lassocS = undefined
  rassocS = undefined

instance BraidedSCat LCirc where
  swapS = undefined

instance MonoidalSCat LCirc where
  LCirc f +++ LCirc g = LCirc $ undefined
  left (LCirc f) = LCirc $ undefined
  right (LCirc g) = LCirc $ undefined


instance CoproductCat LCirc where
  inl = undefined
  inr = undefined
  jam = undefined

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
