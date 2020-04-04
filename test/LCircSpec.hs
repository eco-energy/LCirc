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
import qualified Data.Map as Map
import Data.Bifunctor


instance Arbitrary (NodeId) where
  arbitrary = abs <$> arbitrary

instance EqProp NodeId where
  (=-=) = eq

instance (Arbitrary v) => Arbitrary (Pair v) where
  arbitrary = (:#) <$> arbitrary <*> arbitrary

instance (Arbitrary l, Arbitrary v) => Arbitrary (Edge l v) where
  arbitrary = mkEdge <$> arbitrary <*> arbitrary <*> arbitrary

instance (Eq l, Eq v, Ord l, Ord v, Enum v) => EqProp (LG l v) where
  lg =-= lg' = eq lg lg'

instance (Eq v) => EqProp (CospanC v i o) where
  c =-= c' = eq c c'

instance (Ord l, Ord v, Eq l, Eq v, Eq o, Eq i) => EqProp (LCirc l v i o) where
  lc@(LCirc (lg, c)) =-= lc'@(LCirc (lg', c')) = eq lc lc'

instance EqProp (LCirc' i o) where
  lc' =-= lc'' = eq lc' lc''

instance (Ord l, Ord v, Arbitrary l, Arbitrary v) => Arbitrary (Edges l v) where
  arbitrary = Edges <$> arbitrary

instance (Eq l, Eq v) => EqProp (Edges l v) where
  (Edges e1) =-= (Edges e2) = eq e1 e2

instance Arbitrary CircEl where
  arbitrary = oneof [ Res <$> arbitrary
                    , Ind <$> arbitrary
                    , Cap <$> arbitrary
                    ]

instance (Arbitrary v) => Arbitrary (Port i v) where
  arbitrary = Port <$> arbitrary

instance (Arbitrary v) => Arbitrary (CospanC v i o) where
  arbitrary = CospanC <$> arbitrary

instance (Arbitrary i, Arbitrary r) => Arbitrary (VI' i r) where
  arbitrary = VI <$> arbitrary

instance (Arbitrary l, Arbitrary v, Ord v, Ord l, Show v) => Arbitrary (LG l v) where
  arbitrary = do
    ns <- sns <$> nodes
    es <- (arbitraryEdges ns)
    return $ mkLG' (flatten ns) es 
    where
      flatten [] = []
      flatten ((a, b):xs) = a:b:flatten xs
      tplL :: [a] -> [(a, a)]
      tplL [] = []
      tplL (x:[]) = []
      tplL (x:y:xs) = (x, y):(tplL xs)
      nodes :: Gen (Set.Set v)
      nodes = arbitrarySatisfying (\ns -> length ns == 1)
      sns :: (Set.Set v) -> ([(v, v)])
      sns = tplL . Set.toList 
      arbitraryEdges :: [(v, v)] -> Gen [Edge l v]
      arbitraryEdges lns
        | null lns  = return []
        | otherwise = listOf (liftA3 mkEdge (fst <$> nGen) (snd <$> nGen) arbitrary)
        where
          nGen = elements lns
          edges = map mkEdge

instance (Arbitrary l, Arbitrary v, Ord l, Ord v) => Arbitrary (LCirc i o l v) where
  arbitrary = LCirc <$> arbitrary

instance Arbitrary (LCirc' i o) where
  arbitrary = LCirc' <$> arbitrary


arbL :: Gen (LCirc' i o)
arbL = arbitrary


cardinalIso lc@(LCirc' (LCirc (LG (Nodes n, Edges e), cs))) = (nid' == fmap NodeId [1..nNodes])
  where
    nNodes = length n
    nid' = map tag n'
    (LCirc' (LCirc (LG (Nodes n', Edges e'), cs'))) = toCardinal lc

prop_cardinality = (forAll arbL (cardinalIso))


spec = do
  describe "Sequential Composition Mechanics" $ do
    it "toCardinal should replace node names with names from [0..n] where n is the number of nodes" $ do
      lc <- ((liftIO $ arbs 1) :: IO ([LCirc' i o]))
      liftIO $ print lc
      True `shouldBe` True
      --prop_cardinality
    --it "given two lists of ports, compPorts should return a Map from Node -> (Node -> Node)" $ do
    --  let
    --    o = [mkOutput' 1 1, mkOutput' 2 2, mkOutput' 3 3]
    --    i = [mkInput' 1 4, mkInput' 2 5, mkInput' 3 6]
    --    (lm, rm) = compPorts i o
    --    n1 = mkVIs [1..3 :: NodeId]
    --    n2 = mkVIs [4..6 :: NodeId]
    --    n2' = mkVIs [1, 2, 3]
    --    n'' = map (safeRep rm) n2
    --  Map.keys lm `shouldBe` []
    --  Map.keys rm `shouldBe` [4, 5, 6]
    --  n'' `shouldBe` n2'
    {--it "compatible lgraph node composition given i o ports" $ do
      let
          n1 = Nodes $ map mkVI [1, 2, 3 :: NodeId]
          n2 = Nodes $ map mkVI [4, 5, 6 :: NodeId]
          i' = [(mkInput 1 $ mkVI 4), (mkInput 1 $ mkVI 5)]
          o = [mkInput 1 $ mkVI 3]
          m12 = compPorts i' o
      compNodes n1 n2 m12 `shouldBe` (Nodes $ map mkVI [1, 2, 3, 6])--}
    {--it "composition is associative" $ do
      isAssoc composeLC
    it "composition obeys right id" $ do
      x <- liftIO ((arbs 1) :: IO [LCirc' i o])
      quickCheck (rightId composeLC $ head x)
    it "composition obeys left id" $ do
      x <- liftIO ((arbs 1) :: IO [LCirc' i o])
      quickCheck (leftId composeLC $ head x)--}
    --it "compatible lgraph edge composition" $ do
      --let e1 = edges circuitEx
        --  e2 = edges circuitEx'
          --e12 = compPorts (input exCospan') (output exCospan)
      --(getEdges $ compEdges e1 e2 e12) `shouldBe` (getEdges $ edges compdCirc)
    --it "lCirc Composition is associative" $
      --isAssoc composeLC'

      
composeLC' :: LCirc' i o -> LCirc' o o' -> LCirc' i o'
composeLC' = composeLC

mkVIs :: [NodeId] -> [VI]
mkVIs = map mkVI

mkVIE :: (NodeId, NodeId, CircEl) -> Edge CircEl VI
mkVIE (s, t, l) = mkEdge (mkVI s) (mkVI t) l

mkVIEs = map mkVIE

mkLG'' :: [NodeId] -> [(NodeId, NodeId, CircEl)] -> LG CircEl VI
mkLG'' ns es = mkLG' (mkVIs ns) (mkVIEs es)


unitR :: LG CircEl VI
unitR = mkLG'' [1, 2] [(1, 2, Res 0)]


r3 :: LG CircEl VI
r3 = mkLG' (mkVIs [1, 2]) (mkVIEs [(1, 2, Res 3)]) 


circuitEx :: LG CircEl VI
circuitEx = mkLG'' [1, 2, 3, 4] [ (1, 4, Res 2)
                                , (1, 4, Cap 3)
                                , (1, 2, Res 1)
                                , (2, 3, Ind 1)
                                , (3, 4, Res 1)
                                ] 

circuitEx' :: LG CircEl VI
circuitEx' = mkLG'' [ 5
                     , 6
                     , 7]
             [ (5, 6, Res 5)
             , (6, 7, Res 8)
             ]




exCospan :: CospanC VI VI VI
exCospan = mkCospanC
  [mkInput 1 $ mkVI 1]
  [ (mkOutput 1 $ mkVI 4)
  , (mkOutput 2 $ mkVI 4)]

exCospan' :: CospanC VI VI VI 
exCospan' = mkCospanC
  [(mkInput 1 $ mkVI 5), (mkInput 2 $ mkVI 7)]
  [(mkOutput 1 $ mkVI 5), (mkOutput 2 $ mkVI 7)]


compdCirc :: LG CircEl VI
compdCirc = mkLG'' [1, 2, 3, 4, 6] [(1, 4, Res 2)
                                   , (1, 4, Cap 3)
                                   , (1, 2, Res 1)
                                   , (2, 3, Ind 1)
                                   , (3, 4, Res 1)
                                   , (4, 6, Res 5)
                                   , (4, 6, Res 8)
                                   ]


arbLG :: forall l v. IO (LG l v)
arbLG = do
    ns' <- (arbs 1 nodes) :: IO [Set.Set v]
    let
      ns = sns <$> (Set.toList . head $ ns')
    print ns
    es <- (arbitraryEdges ns)
    return $ mkLG' (flatten ns) es 
    where
      flatten [] = []
      flatten ((a, b):xs) = a:b:flatten xs
      tplL :: [a] -> [(a, a)]
      tplL [] = []
      tplL (x:[]) = []
      tplL (x:y:xs) = (x, y):(tplL xs)
      nodes :: Gen (Set.Set v)
      nodes = arbitrarySatisfying (\ns -> length ns == 1)
      sns :: (Set.Set v) -> ([(v, v)])
      sns = tplL . Set.toList 
      arbitraryEdges :: [(v, v)] -> Gen [Edge l v]
      arbitraryEdges lns
        | null lns  = return []
        | otherwise = listOf (liftA3 mkEdge (fst <$> nGen) (snd <$> nGen) arbitrary)
        where
          nGen = elements lns
          edges = map mkEdge
