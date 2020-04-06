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
import Data.Maybe
import ConCat.Misc
import qualified Data.Either as E
import ConCat.Free.VectorSpace

import ConCat.LGraph
import ConCat.Cospan

-- A category where the morphisms are circuits made of wires with circuit elemtns on them


type LC = LCirc RLC VI

{----------------------------------------------------------------------------------------
         Circuit Elements
----------------------------------------------------------------------------------------}


{---------------------------------------------------------------------------------
    An LCirc is a Pair of an LGraph over a label-set of Circuit Elements
    and a Cospan over the category of Finite Sets.
    Equality for LCirc is defined over an isomorphism class,
    where the names of the nodes of LGraph can be transformed by any mapping (v -> v)
    without affecting the equality of two LCircs.
---------------------------------------------------------------------------------}

data RLC = Res R | Cap R | Ind R deriving (Eq, Ord, Show, Generic)

instance HasRep RLC where
  type Rep (RLC) = (R, R, R) 
  repr (Res r) = (r, 0, 0)
  repr (Cap c) = (0, c, 0)
  repr (Ind i) = (0, 0, i)
  abst (r, 0, 0) = Res r
  abst (0, c, 0) = Cap c
  abst (0, 0, i) = Ind i

instance HasV R RLC

newtype LCirc l v i o = LCirc { runLCirc :: (LG l v, CospanC v i o) } deriving (Eq, Ord, Show, Generic)

newtype LCirc' i o = LCirc' (LCirc RLC VI i o) deriving (Eq, Ord, Show, Generic)


instance (HasRep l, HasRep v, OkLV l v) => HasRep (LCirc l v i o) where
  type Rep (LCirc l v i o) = (Rep (LG l v), Rep (CospanC v i o))
  abst (lg, c) = LCirc (abst lg, abst c)
  repr (LCirc (lg, c)) = (repr lg, repr c)




instance Bifunctor (LCirc l v) where
  bimap f g (LCirc (lg, CospanC (i, o))) = LCirc (lg,
                                                  CospanC (map (portCov f) i,
                                                           map (portCov g) o))

-- Doesn't feel like a semantic function. Maybe it should have a less central name.
lcirc :: (a -> b) -> (LCirc l v) a b
lcirc f = mkLC (mkLG (Nodes Set.empty) (Edges Set.empty)) $ mkCospanC [] []


instance (Ord l, Ord v) => BraidedSCat (LCirc l v)


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

mkLC' :: forall i o. LG RLC VI -> CospanC VI i o -> LCirc' i o 
mkLC' lg cs = LCirc' $ LCirc (lg, cs)

{------------      Serial Composition of LCirc Cospans    --------------------------}

-- This should obey the category laws


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

instance (OkLV l v) => Category (LCirc l v) where
  id = id
  l . l' = (flip composeLC) l l'

instance (OkLV l v) => AssociativeSCat (LCirc l v)

instance (OkLV l v) => MonoidalSCat (LCirc l v) where
  lc +++ lc' = tensorLC' lc lc'

instance (Ord l, Ord v) => CoproductCat (LCirc l v) where
  -- inl :: Ok2 k a b => 
  -- inr :: Ok2 k a b => (LCirc l v) b (Coprod k a b)
  -- jam :: Ok k a => a :+ (LCirc l v a a)
  inl = lcirc inl 
  inr = lcirc inr
  jam = lcirc jam
