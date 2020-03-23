module AlgaSpec where

import Test.QuickCheck.Classes
import Test.QuickCheck hiding (output)
import Test.Hspec
import Test.QuickCheck.Checkers

import Exp

instance Arbitrary (LGraph) -- where
  --arbitrary = LGraph <$> arbitrary

instance EqProp (LGraph) where
  a =-= b = eq a b

instance Arbitrary El where
  arbitrary = oneof [ Res <$> arbitrary
                    , Ind <$> arbitrary
                    , Cap <$> arbitrary
                    , Series <$> arbitrary <*> arbitrary
                    , Parallel <$> arbitrary <*> arbitrary
                    ]  

instance EqProp El where
  (=-=) = eq

instance EqProp Node where
  n1 =-= n2 = eq n1 n2

instance Arbitrary Node where
  arbitrary = Node <$> arbitrary <*> arbitrary <*> arbitrary

spec = do
  describe "Category instance for a labelled graph based on Alga" $ do
    it "monoid laws for Circ" $ do
      verboseBatch (monoid (undefined :: (El)))
