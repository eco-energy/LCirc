{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
module LCircSpec where

import Prelude hiding ((.))
import Test.QuickCheck.Classes
import Test.QuickCheck hiding (output)
import Test.Hspec
import Test.QuickCheck.Checkers
import ConCat.Category hiding (it)


import ConCat.LCirc
import qualified Data.Set as Set
import qualified Data.Map as Map
import ConCat.Pair
import Control.Applicative
import Control.Monad.IO.Class


instance (Arbitrary v) => Arbitrary (Pair v) where
  arbitrary = (:#) <$> arbitrary <*> arbitrary

instance (Arbitrary l, Arbitrary v) => Arbitrary (Edge l v) where
  arbitrary = mkEdge <$> arbitrary <*> arbitrary <*> arbitrary

instance (Eq l, Eq v, Ord l, Ord v, Enum v) => EqProp (LG l v) where
  lg =-= lg' = eq lg lg'

instance (Eq v) => EqProp (CospanC v i o) where
  c =-= c' = eq c c'

instance (Ord l, Ord v, Enum v, Eq l, Eq v) => EqProp (LCirc l v i o) where
  (LCirc lc) =-= (LCirc lc') = eq lc lc' 

instance (Ord l, Ord v, Arbitrary l, Arbitrary v) => Arbitrary (Edges l v) where
  arbitrary = Edges <$> arbitrary

instance (Eq l, Eq v) => EqProp (Edges l v) where
  (Edges e1) =-= (Edges e2) = eq e1 e2

instance Arbitrary RLC where
  arbitrary = Res <$> arbitrary

instance (Arbitrary v) => Arbitrary (CospanC v i o) where
  arbitrary = arbitrary

instance Arbitrary (LG RLC NodeId) where
  arbitrary = do
    ns <- sns
    es <- (arbitraryEdges ns)
    return $ mkLG' (flatten ns) es 
    where
      flatten [] = []
      flatten ((a, b):xs) = a:b:flatten xs
      sns :: Gen [(NodeId, NodeId)]
      sns = (arbitrarySatisfying (\ns -> length ns > 2 && length ns < 5))
      arbitraryEdges :: [(NodeId, NodeId)] -> Gen [Edge RLC NodeId]
      arbitraryEdges lns
        | null lns  = return []
        | otherwise = listOf (liftA3 mkEdge (fst <$> nGen) (snd <$> nGen) arbitrary)
        where
          nGen = elements lns
          edges = map mkEdge

instance Arbitrary (LCirc RLC NodeId i o) where
  arbitrary = LCirc <$> arbitrary

spec = do
  describe "Testing whether an example of an LCirc has coherent semantics" $ do
    it "compatible lgraph node composition" $ do
      let n1 = mkNodes [1, 2, 3 :: NodeId]
          n2 = mkNodes [4, 5, 6 :: NodeId]
          m12 = Map.fromList $ [(5, \c-> if (c == 5) then 1 else c), (4, \c-> if c == 4 then 2 else c)]
      compNodes n1 n2 m12 `shouldBe` (mkNodes [1, 2, 3, 6])
    it "compatible lgraph edge composition" $ do
      let e1 = edges circuitEx
          e2 = edges circuitEx'
          e12 = compPorts (input exCospan') (output exCospan)
          
      (Set.toAscList $ getEdges $ compEdges e1 e2 e12) `shouldBe` (Set.toAscList $ getEdges $ edges compdCirc)
    it "compatible lCirc composition" $ do
      let
        compdCospan :: CospanC NodeId a c
        compdCospan = mkCospanC [mkInput 1 1] [mkOutput 1 4, mkOutput 2 4]
        compdEx :: LCirc RLC NodeId a c
        compdEx = mkLC compdCirc compdCospan
        c12ex :: LCirc RLC NodeId a c
        c12ex = mkLC cr12 cs12 
      (composeLC exLC exLC') `shouldBe` compdEx
      (composeLC lc1 lc2) `shouldBe` lc12
    it "compatible lCirc composition, via category instance" $ do
      (lc2 . lc1) `shouldBe` lc12
      

unitR :: LG RLC NodeId
unitR = mkLG' [1, 2] [mkEdge 1 2 $ Res 0]


r3 :: LG RLC NodeId
r3 = mkLG' [1, 2] [mkEdge 1 2 $ Res 3] 

circuitEx :: LG RLC NodeId
circuitEx = mkLG' [1, 2, 3, 4] [ mkEdge 1 4 $ Res 2
                         , mkEdge 1 4 $ Cap 3
                         , mkEdge 1 2 $ Res 1
                         , mkEdge 2 3 $ Ind 1
                         , mkEdge 3 4 $ Res 1
                         ] 

circuitEx' :: LG RLC NodeId
circuitEx' = mkLG' [5, 6, 7] [ mkEdge 5 6 $ Res 5
                       , mkEdge 6 7 $ Res 8
                       ]


exCospan :: CospanC NodeId a b
exCospan = mkCospanC
  [(mkInput 1 1)]
  [ (mkOutput 1 4)
  , (mkOutput 2 4)] 

exCospan' :: CospanC NodeId b c 
exCospan' = mkCospanC
  [(mkInput 1 5), (mkInput 2 7)]
  [(mkOutput 1 5), (mkOutput 2 7)]

exLC :: LCirc RLC NodeId a b
exLC = mkLC circuitEx exCospan

exLC' :: LCirc RLC NodeId b c
exLC' = mkLC circuitEx' exCospan'

compdCirc :: LG RLC NodeId
compdCirc = mkLG' [1, 2, 3, 4, 6] [ mkEdge 1 4 $ Res 2
                                  , mkEdge 1 4 $ Cap 3
                                  , mkEdge 1 2 $ Res 1
                                  , mkEdge 2 3 $ Ind 1
                                  , mkEdge 3 4 $ Res 1
                                  , mkEdge 4 6 $ Res 5
                                  , mkEdge 4 6 $ Res 8
                                  ]

e1 = [mkEdge 1 2 $ Res 2, mkEdge 1 2 $ Res 3, mkEdge 1 3 $ Res 1, mkEdge 2 3 $ Res 0.9]
cr1 :: LG RLC NodeId
cr1 = mkLG' [1, 2, 3] e1

cs1 = mkCospanC [mkInput 1 1] [mkOutput 1 2, mkOutput 2 2]

lc1 :: LCirc RLC NodeId a b
lc1 = mkLC cr1 cs1



cr2 :: LG RLC NodeId
cr2 = mkLG' [4, 5, 6] [mkEdge 4 5 $ Res 5, mkEdge 6 5 $ Res 8]

cs2 = mkCospanC [mkInput 1 4, mkInput 2 6] [mkOutput 1 5, mkOutput 2 6]

lc2 :: LCirc RLC NodeId b c
lc2 = mkLC cr2 cs2


cr12 :: LG RLC NodeId
cr12 = mkLG' [1, 2, 3, 5] $ e1 ++ [mkEdge 2 5 $ Res 5, mkEdge 2 5 $ Res 8]

cs12 = mkCospanC [mkInput 1 1] [mkOutput 1 5, mkOutput 2 2]


lc12 :: LCirc RLC NodeId a c
lc12 = mkLC cr12 cs12
