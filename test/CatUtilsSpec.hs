{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
module CatUtilsSpec where

import Test.QuickCheck.Classes
import Test.QuickCheck
import Test.Hspec
import Test.QuickCheck.Checkers

import Prelude hiding (either)
import CatUtils


instance Arbitrary a => Arbitrary (Id a) where
  arbitrary = Id <$> arbitrary

instance (Eq a) => EqProp (Id a) where
  a =-= b = eq a b

instance Arbitrary a => Arbitrary (ConstF a) where
  arbitrary = mkConst <$> arbitrary

instance (Eq a) => EqProp (ConstF a) where
  a =-= b = eq a b

instance (Arbitrary a) => Arbitrary (FromInt a) where
  arbitrary = MkFromInt <$> arbitrary

instance (Show a, Arbitrary a, EqProp a) => EqProp (FromInt a) where
  (MkFromInt a) =-= (MkFromInt b) = a =-= b

instance (Arbitrary a) => Arbitrary (Double' a) where
  arbitrary = MkDouble' <$> arbitrary <*> arbitrary

instance (Eq a) => EqProp (Double' a) where
  a =-= b = eq a b

instance (Arbitrary a) => Arbitrary (WString a) where
  arbitrary = WString <$> arbitrary <*> arbitrary

instance (Eq a) => EqProp (WString a) where
  (WString a _) =-= (WString b _) = eq a b

instance Arbitrary (Unit a) where
  arbitrary = return $ U

instance EqProp (Unit a) where
  a =-= b = eq a b

instance (Arbitrary a, Arbitrary b) => Arbitrary (ListPair a b) where
  arbitrary = LP <$> arbitrary

instance (Eq a, Eq b) => EqProp (ListPair a b) where
  a =-= b = eq a b
  
-- Product Type Specializations
t :: (Int -> Int, Int -> Int) -> (Int -> (Int, Int))
t = tuple

ct :: (Int -> Int) ->  (Int -> Int) -> (Int -> (Int, Int))
ct = (&&&)

unt :: (Int -> (Int, Int)) -> (Int -> Int, Int -> Int)
unt = untuple

pairBf :: (Int -> Int) -> (Int -> Int) -> ((Int, Int) -> (Int, Int))
pairBf = bimap

-- Sum Type Specializations
eit :: (Int -> Int) -> (Int -> Int) -> (Either Int Int -> Int)
eit = either

unEit :: (Either Int Int -> Int) -> ((Int -> Int), (Int -> Int))
unEit = unEither

--symMonoidal :: [(String, Property)]
--symMonoidal = [("symmetric", sym), ("associative", assoc), ("leftUnit", leftId), ("rightUnit", rightId)]

spec = do
  describe "functor laws should be obeyed where instances are declared." $ do
    it "Id test" $ do
      verboseBatch (functor (undefined :: (Id (Int, Int, Int))))
    it "const test" $ do
      verboseBatch (functor (undefined :: (ConstF (Int, Int, Int))))
    it "reader functor test" $ do
      verboseBatch (functor (undefined :: (FromInt (Int, Int, Int))))
    it "double arg data constructor functor instance" $ do
      verboseBatch (functor (undefined :: (Double' (Int, Int, Int))))
    it "covariant functor: applies function to first argument of the constructor only" $ do
      verboseBatch (functor (undefined :: (WString (Int, Int, Int))))
    it "unit functor" $ do
      verboseBatch (functor (undefined :: (Unit (Int, Int, Int))))
  --describe "natural transformations" $ do
    --it "" $ do
      --verboseBatch (functor )
    describe "universal constructions for products" $ do
      it "Pair's tuple and untuple are inverses" $
        property $ inverse t unt
      it "curried tuple and untuple are inverses" $
        property $ inverse (uncurry ct) unt
      it "bifunctor instance for pairs is valid - leftId and rightId" $
        property $ involution (pairBf id id)
      it "ListPair is a functor" $ do
        verboseBatch (functor (undefined :: ListPair (Int, Int, Int) (Int, Int, Int)))
    describe "universal constructions for sums" $ do
      it "either and uneither are inverses if either is uncurried" $
        property $ inverse (uncurry eit) unEit
