{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module CircSpec where

import Prelude hiding ((.))
import Test.QuickCheck.Classes
import Test.QuickCheck hiding (output)
import Test.Hspec
import Test.QuickCheck.Checkers

import ConCat.Circ

import ConCat.Category hiding (it)
import ConCat.Rep
import ConCat.Free.VectorSpace hiding (it)
import ConCat.Circuit

instance Arbitrary RLC where
  arbitrary = oneof [Res <$> arbitrary, Cap <$> arbitrary, Ind <$> arbitrary]

spec = do
  describe "LCirc built out of the Circuit Category" $ do
    it "Rep is coherent" $ {--do
      a <- (arbs @RLC ) 10
      let
        vcheck :: RLC -> IO ()
        vcheck r = do
          print $ "actual: " <> (show r)
          print $ "repr: " <> (show $ repr r)
          print $ "abst . repr " <> (show $ (abst @ RLC) . repr $ r)
      mapM (vcheck) a--}
      property $ ((\(x :: RLC) -> (abst . repr $ x) == x))
    it "Vectorspace instance is coherent" $ {--do
      a <- (arbs @RLC ) 10
      let
        vcheck :: RLC -> IO ()
        vcheck r = do
          print $ "actual: " <> (show $ r)
          print $ "toVec: " <> (show $ (toV @Double @RLC) r)
          print $ "unVec . toVec " <> (show $ ((unV @Double @RLC) . (toV @Double @RLC) $ r))
      mapM vcheck a--}
      property $ ((\(x :: RLC) -> ((unV @Double @RLC) . (toV @Double @RLC) $ x) == x))
    it "can generate a simple resistor component" $ do
      let
        --r = namedC "r" @(RLC :> RLC)
        r0 :: RLC :> RLC
        r0 = constC (Res 0)
        brc = (fmapC @(:>) @Blackbox) r0
      --print r
      --print r0
      print brc
      1 `shouldBe` 1
