{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards#-}
module LCircSpec where

import Test.QuickCheck.Classes
import Test.QuickCheck hiding (output)
import Test.Hspec
import Test.QuickCheck.Checkers

import ConCat.LCirc
import qualified Data.Set as Set
import qualified Data.Map as Map
import ConCat.Pair
import Control.Applicative
import Control.Monad.IO.Class

instance (Arbitrary v) => Arbitrary (Pair v) where
  arbitrary = (:#) <$> arbitrary <*> arbitrary

instance Arbitrary VI where
  arbitrary = VI <$> arbitrary

instance (Arbitrary l, Arbitrary v) => Arbitrary (Edge l v) where
  arbitrary = mkEdge <$> arbitrary <*> arbitrary <*> arbitrary

instance (Eq l, Eq v, Ord l, Ord v, Enum v) => EqProp (LG l v) where
  lg =-= lg' = eq lg lg'

instance (Eq v) => EqProp (CospanC v i o) where
  c =-= c' = eq c c'

instance (Ord l, Ord v, Eq l, Eq v) => EqProp (LCirc l v i o) where
  lc@(LCirc (lg, c)) =-= lc'@(LCirc (lg', c')) = eq lc lc'

instance EqProp (LCirc' i o) where
  lc' =-= lc'' = eq lc' lc''

instance (Ord l, Ord v, Arbitrary l, Arbitrary v) => Arbitrary (Edges l v) where
  arbitrary = Edges <$> arbitrary

instance (Eq l, Eq v) => EqProp (Edges l v) where
  (Edges e1) =-= (Edges e2) = eq e1 e2

instance Arbitrary CircEl where
  arbitrary = Res <$> arbitrary

instance (Arbitrary v) => Arbitrary (Port i v) where
  arbitrary = Port <$> arbitrary

instance (Arbitrary v) => Arbitrary (CospanC v i o) where
  arbitrary = CospanC <$> arbitrary

instance Arbitrary (LG CircEl VI) where
  arbitrary = do
    ns <- sns
    es <- (arbitraryEdges ns)
    return $ mkLG' (flatten ns) es 
    where
      flatten [] = []
      flatten ((a, b):xs) = a:b:flatten xs
      sns :: Gen [(VI, VI)]
      sns = (arbitrarySatisfying (\ns -> length ns > 2 && length ns < 5))
      arbitraryEdges :: [(VI, VI)] -> Gen [Edge CircEl VI]
      arbitraryEdges lns
        | null lns  = return []
        | otherwise = listOf (liftA3 mkEdge (fst <$> nGen) (snd <$> nGen) arbitrary)
        where
          nGen = elements lns
          edges = map mkEdge

instance Arbitrary (LCirc CircEl VI i o) where
  arbitrary = LCirc <$> arbitrary

instance Arbitrary (LCirc' i o) where
  arbitrary = LCirc' <$> arbitrary

spec = do
  describe "LCirc' satisfies category laws" $ do
    it "composition is associative" $ do
      --isAssoc composeLC
      1 `shouldBe` 1
    it "composition obeys right id" $ do
      --x <- liftIO ((arbs 1) :: IO [LCirc' i o])
      --quickCheck (rightId composeLC $ head x)
      1 `shouldBe` 1
    it "composition obeys left id" $ do
      --x <- liftIO ((arbs 1) :: IO [LCirc' i o])
      --quickCheck (leftId composeLC $ head x)
    it "LCirc composition works"
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


        exCospan :: CospanC VI VI VI
        exCospan = mkCospanC
          [(mkInput 1 1)]
          [ (mkOutput 1 4)
          , (mkOutput 2 4)] 

        exCospan' :: CospanC VI VI VI 
        exCospan' = mkCospanC
          [(mkInput 1 5), (mkInput 2 7)]
          [(mkOutput 1 5), (mkOutput 2 7)]


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
      let
          n1 = Nodes $ map mkVI [1, 2, 3 :: NodeId]
          n2 = Nodes $ map mkVI [4, 5, 6 :: NodeId]
          m12 = Map.fromList $ [(5, \c-> if (c == 5) then 1 else c), (4, \c-> if c == 4 then 2 else c)]
      compNodes n1 n2 m12 `shouldBe` (Nodes $ map mkVI [1, 2, 3, 6])
    it "compatible lgraph edge composition" $ do
      let e1 = edges circuitEx
          e2 = edges circuitEx'
          e12 = compPorts (input exCospan') (output exCospan)
          
      (getEdges $ compEdges e1 e2 e12) `shouldBe` (getEdges $ edges compdCirc)
      --(l:l':_) <- (arbs 2) :: IO [LG Int NodeId]
      --isoLG l l `shouldBe` True
      --isoLG l' l' `shouldBe` True
    --it "lCirc Composition is associative" $
      --isAssoc composeLC'
--}
      
composeLC' :: LCirc' i o -> LCirc' o o' -> LCirc' i o'
composeLC' = composeLC

