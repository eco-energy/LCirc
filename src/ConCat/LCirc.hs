{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE InstanceSigs #-}
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
import ConCat.AltCat (Diagonal)
import ConCat.Additive
import GHC.Generics ((:.:)(..), Generic)
import Data.Bifunctor
import Data.Finite
import GHC.TypeLits
import Data.Constraint
import Control.Newtype.Generics

import qualified Data.Set as Set
import Data.Set (Set(..))
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map(..))
import ConCat.Circuit
import Data.Maybe
import ConCat.Misc
import qualified Data.Either as E
import ConCat.Free.VectorSpace
import ConCat.Free.LinearRow as L

import ConCat.LGraph
import ConCat.Cospan
import qualified Data.Functor.Rep as Repr

-- A category where the morphisms are circuits made of wires with circuit elemtns on them


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

impedance :: RLC -> R
impedance (Res r) = r
impedance (Cap c) = c
impedance (Ind l) = l


instance HasRep RLC where
  type Rep (RLC) = (Maybe R, Maybe R, Maybe R)
  abst (Just r, Nothing, Nothing) = Res r
  abst (Nothing, Just c, Nothing) = Cap c
  abst (Nothing, Nothing, Just i) = Ind i
  repr (Res r) = (Just r, Nothing, Nothing)
  repr (Cap c) = (Nothing, Just c, Nothing)
  repr (Ind i) = (Nothing, Nothing, Just i)


instance HasV R (Maybe R) where
  type V R (Maybe R) = Maybe :.: V R R
  toV = Comp1 . fmap toV
  unV = fmap unV . unComp1

  
instance HasV R (RLC)
--instance HasV R RLC where


newtype i :-> o = LCirc { runLCirc :: (LG RLC VI, CospanC VI i o) } deriving (Eq, Ord, Show, Generic)

instance Newtype (i :-> o) where
  type O (i :-> o) = (LG RLC VI, CospanC VI i o)
  pack = LCirc
  unpack = runLCirc
--newtype LCirc' i o = LCirc' (LCirc  i o) deriving (Eq, Ord, Show, Generic)


instance  HasRep (i :-> o) where
  type Rep (i :-> o) = (Rep (LG RLC VI), Rep (CospanC VI i o))
  abst (lg, c) = LCirc (abst lg, abst c)
  repr (LCirc (lg, c)) = (repr lg, repr c)



instance Bifunctor (:->) where
  bimap f g (LCirc (lg, CospanC (i, o))) = LCirc (lg,
                                                  CospanC (map (portCov f) i,
                                                           map (portCov g) o))

-- Doesn't feel like a semantic function. Maybe it should have a less central name.
lcirc :: (a -> b) -> a :-> b
lcirc f = mkLC (mkLG (Nodes Set.empty) (Edges Set.empty)) $ mkCospanC [] []



-- For LCirc equality testing, in order to form a category we must have associativety
-- this can only be obtained right now if the equivalence relation between two LCircs counts
-- an isomorphism that is a vertex bijection which is both edge-preserving and label-preserving as equality.
-- Because otherwise the names of the labels end up being muddled up.
-- Semantically, we're working over isomorphism classes of cospans anyways.
-- instance forall l v i o. (Eq l, Eq v, Ord l, Ord v) => Eq (i :-> o) where
--  (LCirc (lg, cs)) == (LCirc (lg', cs')) = iso (toLG' lg) (toLG' lg')
    -- If we defined such a bijection then we can just apply it to all the vertices, all the edges and all the cospans.
    -- If the equivalence relation holds after the bijection, then the graphs are equivalent.
    -- The reason we can


mkLC = curry LCirc

mkLC' :: forall i o. LG RLC VI -> CospanC VI i o -> i :-> o 
mkLC' lg cs = LCirc (lg, cs)

{------------      Serial Composition of LCirc Cospans    --------------------------}

-- This should obey the category laws


composeLC :: forall i o o'. i :-> o -> o :-> o' -> i :-> o'
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

{-- :: i `k` o -> i' `k` o' -> (i :+ i') `k` (o :+ o')
tensorLC :: forall l v i o i' o'. (OkLV l v) => i :-> o -> LCirc i' o' -> LCirc (l :+ l') (v :+ v') (i :+ i') (o :+ o')
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
--}

tensorLC' :: forall i o i' o'. i :-> o -> i' :-> o' -> (i :+ i') :-> (o :+ o')
tensorLC' (LCirc (LG (Nodes n, Edges e), CospanC (i, o))) (LCirc (LG(Nodes n', Edges e'), CospanC (i', o'))) = LCirc (lg'', CospanC (i'', o''))
  where
    n'' = Set.union n n'
    e'' = Set.union e e'
    lg'' = LG (Nodes n'', Edges e'')
    i'' :: Inputs VI (i :+ i')
    i'' = (map (portLeft' @i @i') i) ++ (map (portRight' @i @i') i') 
    o'' :: Outputs VI (o :+ o')
    o'' = (map (portLeft' @o @o') o) ++ (map (portRight' @o @o') o')

inlLC :: i :-> (i :+ o)
inlLC = lcirc inl 

inrLC :: o :-> (i :+ o)
inrLC = lcirc inr

jamLC :: (a :+ a) :-> a
jamLC = lcirc jam
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


instance Category (:->) where
  id = id
  l . l' = (flip composeLC) l l'

instance AssociativeSCat (:->)

instance BraidedSCat (:->)

instance MonoidalSCat (:->) where
  lc +++ lc' = tensorLC' lc lc'

instance CoproductCat (:->) where
  --inl :: (a `LCirc` (a :+ b)) 
  inl =  inlLC
  --inr :: (b `LCirc` (a :+ b))
  inr = inrLC
  --jam :: LCirc (a :+ a) a
  jam = jamLC


--instance Category (LC (LG RLC VI)) where
--  id = IdLC id
--  (PrimLC lg i o) . (PrimLC lg' i' o') = (flip composeLC) (LCirc (lg, CospanC (i, o) )) 


{--
Rules:
  join . split = id
--}

--class (MonoidalSCat k, BraidedSCat) => HypergraphCat k where
  
  


--data Spider m n where

--data Diric :: * -> * -> *

type LinRel s i o = (HasV R i, HasV R o, Diagonal (V R i), Repr.Representable (V R o), Num s)




powerFn :: LG RLC VI -> R
powerFn (LG (Nodes n, Edges e)) = (1 / 2) * (sum $ Set.map edgePower e)
  where
    edgePower :: Edge RLC VI -> R
    edgePower (Edge
               (((VI(_, v :# i)) :# (VI(_, v' :# i')))
              , l)) = (1 / impedance l) * ((v' - v) **2)


data LinearCirc lc = LinCirc {unLinC :: lc} deriving (Generic, Functor)

toLinC :: (f i :-> g o) -> (f :-* g) o
toLinC = undefined

instance OkFunctor (:->) (LinearCirc) where
  okFunctor = Entail (Sub Dict)

instance FunctorCat (:->) (LinearCirc) where
  fmapC = undefined --toLinC
  unzipC = undefined


{--
data FinCospan :: * -> * -> * -> * where
  IdFC :: FinCospan lg i o
  PrimFC :: lg -> i -> o -> FinCospan lg i o
  CoprodFC :: FinCospan lg i o -> FinCospan lg i' o' -> FinCospan lg (i :+ i')  (o :+ o')
  ComposeFC :: FinCospan lg i oi -> FinCospan lg oi o' -> FinCospan lg i o'
  ProdFC :: FinCospan lg i o :* FinCospan lg' i' o' -> FinCospan lg (i :* i') (o :* o')
  SwapFC :: (FinCospan lg) i o -> (FinCospan lg) o i
  

--instance Frob (LC lg) where
--  unit k = PrimLC k () ()
  
instance Category (FinCospan c) where
  id = IdFC
  (.) = flip ComposeFC

instance MonoidalSCat (FinCospan c) where
  lc +++ lc' = CoprodFC lc lc'

instance MonoidalPCat (FinCospan c) where
  (***) = curry ProdFC

instance ProductCat (FinCospan c)
  exl = (id, )

instance BraidedPCat (FinCospan c) where
  swapP = SwapFC

instance CoproductPCat (FinCospan c) where
  --inl = CoprodFC


--instance (HasRep g, HasRep i, HasRep o) => HasRep (LC g i o) where
--  type Rep (LC g i o) = ((Rep g, Rep i, Rep o))
--  repr (PrimLC lg i o) = (repr lg, repr i, repr o)
--  repr (Coprod (PrimLC g i o)  (PrimLC g' i' o')) = (repr g g), repr b)

--}
