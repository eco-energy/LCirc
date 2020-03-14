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

import Prelude hiding (id, (.), uncurry, curry)
import qualified Prelude as P

import ConCat.Category
import ConCat.Pair
import ConCat.Rep
import GHC.Generics (Generic)
import Data.Bifunctor
import qualified ConCat.Additive as A
import Data.Finite
import GHC.TypeLits (KnownNat(..))
import qualified Data.Set as Set
import Data.Set (Set(..))
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map(..))

-- A category where the morphisms are circuits made of wires with circuit elemtns on them



-- A graph is a finite set E of edges and a finite set N of nodes equipped with a pair of functions s,t: E -> N,
-- assigning to each edge its source and target. e is an edge from s(e) to t(e). An lgraph has an additional function
-- l: E -> L assigning a label to each edge.


-- A network, such as an electrical circuit, with m inputs and n outputs is a morphism from m to n,
-- while putting networks together in series is composition, and setting them side by side is tensoring.

-- Each kind of network corresponds to a mathematically natural prop.


{----------------------------------------------------------------------------------------
         Labelled Graphs where vertices are finite sets and edges have a label
----------------------------------------------------------------------------------------}
type R = Double

newtype Edge l v = Edge (Pair v, l) deriving (Show, Generic)

mkEdge :: v -> v -> l -> Edge l v
mkEdge s t l = Edge (s :# t, l)

replaceMatching :: (Eq v) => Maybe (v -> v) -> Maybe (v -> v) -> Edge l v ->  Edge l v
replaceMatching (Just f) (Just g) e@(Edge (s :# t, l)) = (Edge (f s :# g t, l))
replaceMatching (Just f) Nothing e@(Edge (s :# t, l)) = (Edge (f s :# t, l))
replaceMatching Nothing (Just g) e@(Edge (s :# t, l)) = (Edge (s :# g t, l))
replaceMatching Nothing Nothing e@(Edge (s :# t, l)) = e


replaceEdges :: (Ord v, Ord l) => Edges l v -> Edges l v -> Map v (v -> v) -> Edges l v
replaceEdges e1 e2 e12 = Set.union e1 e2'
  where
    e2' = Set.map re e2
    re e = replaceMatching (Map.lookup (src e) e12) (Map.lookup (tgt e) e12) e

getFn :: (Ord v) => Map v (v -> v) -> v -> Maybe (v -> v)
getFn fnMap n = Map.lookup n fnMap

instance (Eq l, Eq v) => Eq (Edge l v) where
  (Edge (a :# b, l)) == (Edge (a' :# b', l')) = (a == a' && b == b' || a == b' && b == a') && l == l'

instance (Ord l, Ord v) => Ord (Edge l v) where
  (Edge (a :# b, l)) <= (Edge (a' :# b', l')) = (a, b, l) <= (a', b', l')

type Edges l v = Set (Edge l v)

type Nodes v = Set v

newtype LG l v = LG { runLG :: (Nodes v, Edges l v) } deriving (Eq, Show, Generic)

nodes :: LG l v -> Nodes v
nodes = fst . runLG

edges :: LG l v -> Edges l v
edges = snd . runLG

mkLG :: Nodes v -> Edges l v -> LG l v
mkLG = curry LG

mkNodes :: (Ord v) => [v] -> Nodes v
mkNodes = Set.fromList

mergeNodes :: (Ord v) => Nodes v -> Nodes v -> Map v (v -> v) -> Nodes v
mergeNodes n n' chngs = Set.union n n'_
  where
    n'_ = foldl (\k nn-> Set.delete nn k) n' (Map.keys chngs)

mkEdges :: (Ord v, Ord l) => [Edge l v] -> Edges l v
mkEdges = Set.fromList


src :: Edge l v -> v
src (Edge (s :# _, _)) = s

tgt :: Edge l v -> v
tgt (Edge (_ :# t, _)) = t

label :: Edge l v -> l
label (Edge (_, l)) = l


{---------------------------------------------------------------------------------
    Cospans in a Category
---------------------------------------------------------------------------------}
{--
newtype Cospan v i o = Cospan
  { runCospan :: (i -> v, o -> v, [v]) } deriving (Generic)

mkCospan :: (i -> v) -> (o -> v) -> [v] -> Cospan v i o
mkCospan i o vs = Cospan (i, o, vs)

compCospan :: (Eq v) => Cospan v i o -> Cospan v o o' -> Cospan v i o
compCospan (Cospan (f, g, vs)) (Cospan (h, k, vs')) = mkCospan (iN . f) (iP . g) vs''
  where
    iP = undefined
    iN = undefined
    vs'' = identify vs vs'
--}

{-------------------------
     Operadic Machinery
--------------------------}

data Nat = Z | S Nat deriving (Show)

type One = S Z
type Two = S (S Z)
type Three = S (S (S Z))

data CIdx n where
  CS0 :: CIdx Z
  CSCons :: CIdx n -> CIdx (S n)
---------------------------------}

type PortId = Int
type NodeId = Int

data Port v a = Port (PortId, v) deriving (Eq, Ord, Show)

unifyPorts :: (Eq v) => Port v a -> Port v a -> (v, (v -> v))
unifyPorts (Port (p, n)) (Port (p', n')) = (n', (\c -> if c == n' then n else c)) 

unifyComposablePortSets ::  (Ord v) => Inputs v i -> Outputs v i -> Map v (v -> v)
unifyComposablePortSets is os = Map.fromList $ map (uncurry unifyPorts) $ zip os is 

type Inputs v a = [Port v (CIdx a)]
type Outputs v a = [Port v (CIdx a)]


--cmpC :: Cospan k v i o -> Cospan k v o o' -> Cospan k v i o'
--cmpC (Cospan (i, o)) (Cospan (i', o')) = 

newtype CospanC v i o = CospanC (Inputs v i, Outputs v o)

mkCospanC :: Inputs v i -> Outputs v o -> CospanC v i o
mkCospanC = curry CospanC

--mkCospanC' :: [Port (CIdx i)] -> [Port (CIdx o)] -> CospanC i o
--mkCospanC' is os = mkCospanC (Set.fromList is) (Set.fromList os)


{---------------------------------------------------------------------------------
    An LCirc is a Pair of an LGraph over a label-set of Circuit Elements
    and a Cospan over the category of Finite Sets.
---------------------------------------------------------------------------------}

data CircEl = Res R | Cap R | Ind R deriving (Eq, Ord, Show, Generic)

newtype LCirc l v i o = LCirc { runLCirc :: (LG l v, CospanC v i o) } deriving (Generic)

instance (Show l, Show v) => Show (LCirc l v i o) where
  show (LCirc (lg, CospanC (i, o))) = "LCirc: " <> (show lg)

instance (Eq l, Eq v) => Eq (LCirc l v i o) where
  (LCirc (lg, CospanC (i, o))) == (LCirc (lg', CospanC (i', o'))) = lg == lg'
    && i == i'
    && o' == o'

mkLC = curry LCirc

input :: CospanC v i o -> Inputs v i
input (CospanC (i, _)) = i

output :: CospanC v i o -> Outputs v o
output (CospanC (_, o)) = o


composeLC :: (Ord v, Ord l) => LCirc l v i o -> LCirc l v o o' -> LCirc l v i o'
composeLC (LCirc ((LG (n, e)), CospanC (i, o))) (LCirc ((LG (n', e')), CospanC (i', o'))) = mkLC lg'' cspan''
  where
    --unifyComposablePortSets :: Inputs v i -> Outputs i -> Map NodeId (NodeId -> NodeId)
    replacements = unifyComposablePortSets i' o 
    lg'' = LG (mergeNodes n n' replacements, replaceEdges e e' replacements)
    o'' = map (\(Port (pid, nid)) -> case Map.lookup nid replacements of
                  Just nid' -> Port (pid, nid' nid)
                  Nothing -> Port (pid, nid)
              ) o'
    cspan'' = CospanC (i, o'')

mkLG' ns es = mkLG (mkNodes ns) $ mkEdges es 

unitR :: LG CircEl NodeId
unitR = mkLG' [1, 2] [mkEdge 1 2 $ Res 0]


r3 :: LG CircEl NodeId
r3 = mkLG' [1, 2] [mkEdge 1 2 $ Res 3] 

circuitEx :: LG CircEl NodeId
circuitEx = mkLG' [1, 2, 3, 4] [ mkEdge 1 4 $ Res 2
                               , mkEdge 1 4 $ Cap 3
                               , mkEdge 1 2 $ Res 1
                               , mkEdge 2 3 $ Ind 1
                               , mkEdge 3 4 $ Res 1
                               ] 

circuitEx' :: LG CircEl NodeId
circuitEx' = mkLG' [5, 6, 7] [ mkEdge 5 6 $ Res 5
                             , mkEdge 6 7 $ Res 8
                             ]
mkPort = curry Port
mkInput = mkPort
mkOutput = mkPort

exCospan :: CospanC NodeId One Two
exCospan = mkCospanC
  [(mkInput 1 1)]
  [ (mkOutput 1 4)
  , (mkOutput 2 4)] 

exCospan' :: CospanC NodeId Two Three 
exCospan' = mkCospanC
  [(mkInput 1 5), (mkInput 2 7)]
  [(mkOutput 1 5), (mkOutput 2 7)]

exLC :: LCirc CircEl NodeId One Two
exLC = mkLC circuitEx exCospan

exLC' :: LCirc CircEl NodeId Two Three
exLC' = mkLC circuitEx' exCospan'




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

