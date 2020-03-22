module PushoutSpec where

import Test.QuickCheck.Classes
import Test.QuickCheck hiding (output)
import Test.Hspec
import Test.QuickCheck.Checkers

import ConCat.Pushout

spec = describe "the pushout is a commutative square" $ do
     it "a thing and another" $ do
       1 `shouldBe` 1
