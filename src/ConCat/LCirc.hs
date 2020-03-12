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

instance (Eq l, Eq v) => Eq (Edge l v) where
  (Edge (a :# b, l)) == (Edge (a' :# b', l')) = a == a' && b == b' && l == l'

type Edges l v = [Edge l v]

type Nodes v = [v]

newtype LG l v = LG { runLG :: (Nodes v, Edges l v) } deriving (Eq, Show, Generic)

mkLG :: Nodes v -> Edges l v -> LG l v
mkLG = curry LG

src :: Edge l v -> v
src (Edge (s :# _, _)) = s

tgt :: Edge l v -> v
tgt (Edge (_ :# t, _)) = t

label :: Edge l v -> l
label (Edge (_, l)) = l


{---------------------------------------------------------------------------------
    Cospans in a Category
---------------------------------------------------------------------------------}

newtype Cospan k v i o = Cospan { runCospan :: (i `k` v, o `k` v) } deriving (Generic, Show)

mkCospan :: i `k` v -> o `k` v -> Cospan k v i o
mkCospan = curry Cospan

instance (Category k, Ok k v) => Category (Cospan k v)


data Port a = Input (Int, Int) | Output (Int, Int) deriving (Show)

type Inputs a = [Port (CIdx a)]
type Outputs a = [Port (CIdx a)]


--cmpC :: Cospan k v i o -> Cospan k v o o' -> Cospan k v i o'
--cmpC (Cospan (i, o)) (Cospan (i', o')) = 

type CospanC i o = Cospan (->) (Nodes Int) (Inputs i) (Outputs o)



{---------------------------------------------------------------------------------
    An LCirc is a Pair of an LGraph over a label-set of Circuit Elements
    and a Cospan over the category of Finite Sets.
---------------------------------------------------------------------------------}

newtype LCirc l v i o = LCirc (LG l v, CospanC i o) deriving (Generic)

instance (Show l, Show v) => Show (LCirc l v i o) where
  show (LCirc (lg, Cospan (i, o))) = "LCirc: " <> (show lg)

instance (Eq l, Eq v) => Eq (LCirc l v i o) where
  (LCirc (lg, Cospan (i, o))) == (LCirc (lg', Cospan (i', o'))) = lg == lg'

mkLC = curry LCirc


input :: Cospan k v i o -> i `k` v
input (Cospan (i, _)) = i

output :: Cospan k v i o -> o `k` v
output (Cospan (_, o)) = o

unitR :: LG CircEl Int
unitR = mkLG [1, 2] [mkEdge 1 2 $ Res 0]

data CircEl = Res R | Cap R | Ind R deriving (Eq, Ord, Show, Generic)



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


r3 :: LG CircEl Int
r3 = mkLG [1, 2] [mkEdge 1 2 $ Res 3] 

circuitEx :: LG CircEl Int
circuitEx = mkLG [1, 2, 3, 4] [ mkEdge 1 2 $ Res 2
                              , mkEdge 1 2 $ Cap 3
                              , mkEdge 1 3 $ Res 1
                              , mkEdge 3 4 $ Ind 1
                              , mkEdge 4 2 $ Res 1
                              ] 

circuitEx' :: LG CircEl Int
circuitEx' = mkLG [5, 6, 7] [ mkEdge 5 6 $ Res 5
                            , mkEdge 6 7 $ Res 8
                            ]



{-------------------------
 Operadic Circuit Cospans
--------------------------}


intCospan :: [Port (CIdx i)] -> [Port (CIdx o)] -> CospanC i o
intCospan is os = (mkCospan (\_ -> map getI is) (\_ -> map getO os))
  where
    getI (Input (_, n)) = n
    getO (Output (_, n)) = n

mkInput = curry Input
mkOutput = curry Output

exCospan :: CospanC One Two
exCospan = intCospan
  [(mkInput 1 1)]
  [ (mkOutput 1 2)
  , (mkOutput 2 2)] 

exCospan' :: CospanC Two Three 
exCospan' = intCospan
  [(mkInput 1 5), (mkInput 2 7)]
  [(mkOutput 1 5), (mkOutput 2 7)]

exLC :: LCirc CircEl Int One Two
exLC = mkLC circuitEx exCospan

exLC' :: LCirc CircEl Int Two Three
exLC' = mkLC circuitEx' exCospan'

composeLC :: LCirc l v i o -> LCirc l v o o' -> LCirc l v i o'
composeLC (LCirc (lg, Cospan (i, o))) (LCirc (lg', Cospan (i', o'))) = mkLC lg'' cspan''
  where
    -- For a list of nodes, get all the edges
    lg'' = compLG o i' lg lg'
    cspan'' = undefined --compCS cspan cspan'

compLG :: (Outputs i -> Nodes Int) -> (Inputs i -> Nodes Int) -> LG l v -> LG l v -> LG l v
compLG o i' lg lg' = undefined


compCS :: Cospan k v i o -> Cospan k v o o' -> Cospan k v i o'
compCS (Cospan (i, o)) (Cospan (i', o')) = mkCospan i o'

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

