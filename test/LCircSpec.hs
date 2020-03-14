{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
module LCircSpec where

import Test.QuickCheck.Classes
import Test.QuickCheck hiding (output)
import Test.Hspec
import Test.QuickCheck.Checkers

import ConCat.LCirc
import qualified Data.Set as Set
import qualified Data.Map as Map
import ConCat.Pair

instance (Arbitrary v) => Arbitrary (Pair v) where
  arbitrary = (:#) <$> arbitrary <*> arbitrary

instance (Arbitrary l, Arbitrary v) => Arbitrary (Edge l v) where
  arbitrary = mkEdge <$> arbitrary <*> arbitrary <*> arbitrary

spec = do
  describe "Testing whether an example of an LCirc has coherent semantics" $ do
    let
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

      compdCirc :: LG CircEl NodeId
      compdCirc = mkLG' [1, 2, 3, 4, 6] [ mkEdge 1 4 $ Res 2
                                        , mkEdge 1 4 $ Cap 3
                                        , mkEdge 1 2 $ Res 1
                                        , mkEdge 2 3 $ Ind 1
                                        , mkEdge 3 4 $ Res 1
                                        , mkEdge 4 6 $ Res 5
                                        , mkEdge 4 6 $ Res 8
                                        ]
      
    it "compatible lgraph node composition" $ do
      let n1 = Set.fromList [1, 2, 3 :: NodeId]
          n2 = Set.fromList [4, 5, 6 :: NodeId]
          m12 = Map.fromList $ [(5, \c-> if (c == 5) then 1 else c), (4, \c-> if c == 4 then 2 else c)]
      mergeNodes n1 n2 m12 `shouldBe` (Set.fromList [1, 2, 3, 6])
    it "compatible lgraph edge composition" $ do
      let e1 = edges circuitEx
          e2 = edges circuitEx'
          e12 = unifyComposablePortSets (input exCospan') (output exCospan)
          
      (Set.toAscList $ replaceEdges e1 e2 e12) `shouldBe` (Set.toAscList $ edges compdCirc)
    it "compatible lCirc composition" $ do
      let
        compdCospan :: CospanC NodeId One Three
        compdCospan = mkCospanC [mkInput 1 1] [mkOutput 1 4, mkOutput 2 6]
        compdEx :: LCirc CircEl NodeId One Three
        compdEx = mkLC compdCirc compdCospan
      (composeLC exLC exLC') `shouldBe` compdEx
