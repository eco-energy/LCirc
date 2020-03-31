{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
module AlgebraSpec where

import ConCat.Algebra
import Test.QuickCheck.Classes
import Test.QuickCheck hiding (output)
import Test.Hspec
import Test.QuickCheck.Checkers
import ConCat.Additive

-- instance Arbitrary 
-- type R = Double

errorDecreasing :: (s -> s -> s) -> (s -> s -> s) -> s -> s -> Bool
errorDecreasing e e' s s' = ((\s s' -> e s s') s) >= ((\s s' -> e' s s') s)
  

monotonic :: (Num a, Arbitrary a) => Gen ([a])
monotonic = arbitrarySatisfying (\fs -> yes fs)
  where
    yes :: [a] -> Bool
    yes fs = scanl (<=) True fs
    f :: a -> a -> Bool
    f = p 

spec = do
  describe "Learner Can Follow a Path" $ do
    it "" $ do
      1 `shouldBe` 1
      
