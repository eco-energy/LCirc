{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
module LCircSpec where

import Test.QuickCheck.Classes
import Test.QuickCheck
import Test.Hspec
import Test.QuickCheck.Checkers

import ConCat.LCirc

spec = do
  describe "Testing whether an example of an LCirc has coherent semantics" $ do
    it "Cospan Composition" $ do
      let
        compdCirc :: LG CircEl Int
        compdCirc = mkLG [1, 2, 3, 4, 6] [ mkEdge 1 2 $ Res 2
                                         , mkEdge 1 2 $ Cap 3
                                         , mkEdge 1 3 $ Res 1
                                         , mkEdge 3 4 $ Ind 1
                                         , mkEdge 4 2 $ Res 1
                                         , mkEdge 4 6 $ Res 5
                                         , mkEdge 4 6 $ Res 8
                                         ]
        compdCospan :: CospanC One Three
        compdCospan = intCospan [mkInput 1 1] [mkOutput 1 4, mkOutput 2 6]
        compdEx :: LCirc CircEl Int One Three
        compdEx = mkLC compdCirc compdCospan

      (composeLC exLC exLC') `shouldBe` compdEx
