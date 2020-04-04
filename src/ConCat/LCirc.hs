{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
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
{-# LANGUAGE ScopedTypeVariables #-}
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
import qualified ConCat.TArr as T

-- A category where the morphisms are circuits made of wires with circuit elemtns on them

newtype NodeId = NodeId Int deriving (Eq, Ord, Show, Generic, Enum, Num)

instance HasRep NodeId where
  type Rep NodeId = Int
  abst  = NodeId
  repr (NodeId i) = i

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


mkPort :: PortId -> v -> Port i v
mkPort = curry Port

mkVIPort :: PortId -> NodeId -> Port i VI
mkVIPort p n = mkPort p $ mkVI n

mkInput :: PortId -> v -> Port i v
mkInput = mkPort

mkInput' = mkVIPort
mkOutput' = mkVIPort

mkOutput :: PortId -> v -> Port o v
mkOutput = mkPort


type Inputs v a = [Port a v]
type Outputs v a = [Port a v]

newtype Cospan k v = Cospan (v `k` v, v `k` v) deriving (Generic)

newtype CospanC v i o = CospanC { unCspanC :: ([Port i v], [Port o v]) } deriving (Eq, Ord, Show, Generic)

instance HasRep (CospanC v i o) where
   type Rep (CospanC v i o) = CospanC v i o
   abst = id
   repr = id


mkCospanC :: Inputs v i -> Outputs v o -> CospanC v i o
mkCospanC = curry CospanC


mkCospanLG :: [v] -> [v] -> CospanC v i o
mkCospanLG inputs outputs = CospanC (iports, oports)
  where
    iports = map (uncurry mkInput) $ zip [1..] inputs
    oports = map (uncurry mkOutput) $ zip [1..] outputs


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

{----------------------------------------------------------------------------------------
         Circuit Elements
----------------------------------------------------------------------------------------}



data CircEl = Res R | Cap R | Ind R deriving (Eq, Ord, Show, Generic)

instance HasRep CircEl where
  type Rep (CircEl) = (Int, R) 
  repr (Res r) = (1, r)
  repr (Cap c) = (2, c)
  repr (Ind i) = (3, i)
  abst (1, el) = Res el
  abst (2, el) = Cap el
  abst (3, el) = Ind el

    
newtype LCirc i o l v = LCirc { runLCirc :: (LG l v, CospanC v i o) } deriving (Eq, Ord, Show, Generic)

newtype LCirc' i o = LCirc' (LCirc i o CircEl VI) deriving (Eq, Ord, Show, Generic)

instance Bifunctor (LCirc i o) where
  bimap :: forall a b c d i o. (a -> b) -> (c -> d) -> LCirc i o a c -> LCirc i o b d
  bimap f g (LCirc (LG (nodes, edges), CospanC (i, o))) = LCirc (LG (n', e'), CospanC (i', o'))
    where
      n' :: Nodes d
      n' = fmap g nodes
      e' :: Edges b d
      e' = bimap f g edges
      i' :: [Port i d]
      i' = map (fmap g) i
      o' :: [Port o d]
      o' = map (fmap g) o

instance Bifunctor (LCirc') where
  bimap :: forall i o i' o'. (i -> i') -> (o -> o') -> LCirc' i o -> LCirc' i' o'
  bimap f g (LCirc' (LCirc ((LG (n, e)), (CospanC (i, o))))) = LCirc' (LCirc ((LG (n', e')), CospanC (map i' i, map o' o)))
    where
      n' :: Nodes VI
      n' = id n
      e' :: Edges CircEl VI
      e' = id e
      i' :: Port i VI -> Port i' VI
      i' = changePort
      o' :: Port o VI -> Port o' VI
      o' = changePort
      changePort :: Port a VI -> Port a' VI
      changePort (Port (pid, vi)) = mkPort pid vi
  

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


instance (HasRep l, HasRep v) => HasRep (LCirc i o l v ) where
  type Rep (LCirc i o l v) = (LG l v, CospanC v i o)
  abst = LCirc
  repr (LCirc a) = a

instance HasRep (LCirc' i o) where
  type Rep (LCirc' i o) = (LG CircEl VI, CospanC VI i o)
  abst =  LCirc' . LCirc
  repr (LCirc' (LCirc a)) = a

instance Category LCirc' where
  type Ok (LCirc') = (Ord)
  id = id
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
    (lm, rm) = compPorts i' o
    lg'' = LG (compNodes n n' lm rm, compEdges e e' lm rm)
    o'' = map quotient o'
    cspan'' = CospanC (i, o'')
    quotient (Port(pid, vi@(VI (nid, _)))) = case Map.lookup nid (Map.union lm rm) of
                  Just f -> Port (pid, f vi)
                  Nothing -> Port (pid, vi)

compNodes :: Nodes VI -> Nodes VI -> Map NodeId (VI -> VI) -> Map NodeId (VI -> VI) -> Nodes VI
compNodes (Nodes []) (Nodes []) _ _ = Nodes []
compNodes (Nodes a) (Nodes []) lma _ = Nodes $ map (safeRep lma) a
compNodes (Nodes n) (Nodes n') lma rma = fromNodeSet $ Set.union ln rn
  where
    ln = Set.fromList $ map (safeRep lma) n
    rn =  Set.fromList $ map (safeRep rma) n'

safeRep :: Map NodeId (VI -> VI) -> VI -> VI
safeRep m v@(VI(i, vi)) = case Map.lookup i m of
                        Nothing -> v
                        Just f -> f v    

compEdges :: Edges CircEl VI
  -> Edges CircEl VI
  -> Map NodeId (VI -> VI)
  -> Map NodeId (VI -> VI)
  -> Edges CircEl VI
compEdges e1 e2 lm rm = fromEdgeSet $ Set.union e1' e2'
  where
    e1' = Set.map (re lm) (toEdgeSet e1)
    e2' = Set.map (re rm) (toEdgeSet e2)
    re m e = replaceMatching (Map.lookup (srcId e) m) (Map.lookup (tgtId e) m) e
    replaceMatching :: Maybe (VI -> VI) -> Maybe (VI -> VI)
                    -> Edge CircEl VI ->  Edge CircEl VI
    replaceMatching (Just f) (Just g) e@(Edge (s :# t, l)) = (Edge (f s :# g t, l))
    replaceMatching (Just f) Nothing e@(Edge (s :# t, l)) = (Edge (f s :# t, l))
    replaceMatching Nothing (Just g) e@(Edge (s :# t, l)) = (Edge (s :# g t, l))
    replaceMatching Nothing Nothing e@(Edge (s :# t, l)) = e



compPorts :: forall i o.  Inputs VI i -> Outputs VI i -> (Map NodeId (VI -> VI), Map NodeId (VI -> VI))
--compPorts [] [] = (Map.empty, Map.empty)
--compPorts is [] = (Map.empty, Map.empty)
compPorts is os = unifyPorts os is
  -- inputs is [Port (p, n)] and so is outputs.
  -- we want to IDENTIFY.
  -- IDENTIFY collapses nodes.
  -- each port can be connected to multiple inputs and multiple outputs
  -- We choose the label of the ordinally lowest output as the label of the identified node
  -- Then we replace the labels of all the nodes identified with that port with the label
  -- of the identified node.

unifyPorts :: Outputs VI i -> Inputs VI i -> (Map NodeId (VI -> VI), Map NodeId (VI -> VI))
unifyPorts [] [] = (Map.empty, Map.empty)
unifyPorts ((Port (p, n)):os) is = (Map.union omap orec, Map.union imap irec)
  where
    (orec, irec) = unifyPorts irem orem
    ident (Port (p', i)) = p /= p'
    o' = filter (ident) os
    orem = filter (not . ident) os
    i' = filter (ident) is
    irem = filter (not . ident) is
    idents = concat [o', i']
    (Port (_, vLabel)) = minimumBy (\(Port (_, v)) (Port (_, v')) -> compare (tag v) (tag v')) idents
    omap = Map.fromList [(nid, (\v -> if v == v' then vLabel else v)) | (Port (_, v'@(VI(nid, _)))) <- o']
    imap = Map.fromList [(nid, (\v -> if v == v' then vLabel else v)) | (Port (_, v'@(VI(nid, _)))) <- i']


toCardinal :: LCirc' i o -> LCirc' i o
toCardinal (LCirc' (LCirc (lg, cs))) = LCirc' $ LCirc (LG (ns', es'), CospanC (is', os'))
  where
    es' = bimap id safeLookupVI es
    ns' = Nodes $ fmap (bimap safeLookup id) ns
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




{-------- An Endofunctor is a map from Hask-to-Hask ----------}
endoF :: (Bifunctor k) => (a -> a') -> (b -> b') ->  k a b -> k a' b'
endoF f g = bimap f g

endoLC :: (a -> a') -> (b -> b') -> (LCirc i o a b) -> (LCirc i o a' b')
endoLC = endoF


class (T.HasFin a, T.HasFin b) => OkLC a b c



{--
identify :: [PortId, (NodeId, NodeId)] -> LG l v -> LG l v
identify = 
--}

