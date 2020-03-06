{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
module CatUtils where

import Prelude

-- A category theory toolbox
--import ConCat.Pair

-- general purpose Identity?
data Id a = Id a deriving (Eq, Show)

mkId = Id
unId (Id a) = a

instance Functor Id where
  fmap f = mkId . f . unId


-- Here all the types defined by passing a specific a to ConstF are isomorphic.
-- Naturally Isomorphic
data ConstF a = MkConst Int deriving (Eq, Show)

mkConst :: forall a. Int -> ConstF a
mkConst i = MkConst i

unConst :: forall a. ConstF a -> Int
unConst (MkConst i) = i

instance Functor ConstF where
  --fmap :: forall a b. (a -> b) -> ConstF a -> ConstF b
  fmap _ (MkConst i) = mkConst i

-- Reader Functor
-- FromInt that takes a type a and returns the function type Int -> a

data FromInt a = MkFromInt (Int -> a)

mapFromInt :: (a -> b) -> (FromInt a -> FromInt b)
mapFromInt f (MkFromInt g) = MkFromInt (f . g)

instance Functor FromInt where
  fmap = mapFromInt

instance Show (FromInt a) where
  show _ = "FromInt: Int -> a"



-- Functor Examples
data Double' a = MkDouble' a a deriving (Eq, Show)
data WString a = WString a String deriving (Eq, Show)
data Unit a = U deriving (Eq, Show)

instance Functor Double' where
  fmap f (MkDouble' a a') = MkDouble' (f a) (f a')

instance Functor WString where
  fmap f (WString a s) = WString (f a) s

instance Functor Unit where
  fmap f _ = U



-- natTrans :: forall a. f a -> g a
type f ~> g = forall a. f a -> g a

type f <~ g = forall a. g a -> f a

infix 0 ~>

infix 0 <~


--applyNatTrans :: forall f g a. (Functor f, Functor g) => (f ~> g) -> f a
applyNatTrans :: forall f g a. (Functor f, Functor g) => (f ~> g) -> f a -> g a
applyNatTrans nt = nt

type IdToConst = Id ~> ConstF

singleton :: Id ~> []
singleton (Id a) = [a]

-- all natural transformations from the Id endofunctor
-- to the const endofunctor is constant
-- forall alpha there is some Natural Number `n` s.t
-- forall x alpha_x : X -> N = const n
constNF :: Int -> (Id ~> ConstF)
constNF i b = MkConst $ const i b


{----------------------------------------------------------
               Universal Constructions
-----------------------------------------------------------}

{-$ PRODUCTS $-}

-- data Pair a b = MkPair a b

--pair :: a -> b -> Pair a b
--pair = MkPair

-- $ using the universal property of products.
tuple :: (c -> a, c -> b) -> (c -> (a, b))
tuple (f, g) c = (f c, g c)

untuple :: (c -> (a, b)) -> (c -> a, c -> b)
untuple h = (\c -> fst $ h c, \c -> snd $ h c)

-- $ curried version of tuple
(&&&) :: (c -> a) -> (c -> b) -> (c -> (a, b))
(&&&) = curry tuple

-- The product is a functor if every pair of objects in
-- a category C has a product.
-- It is a functor in 2 arguments, ergo the following typeclass

-- $ works on typeconstructors that have two arguments
--   has an analogue of fmap that asks for 2 functions
class Bifunctor f where
  bimap :: (a -> a') -> (b -> b') -> (f a b -> f a' b')

-- $ The instance of Bifunctor on products gives
--   us the symmetric monoidal structure on the category
instance Bifunctor (,) where
  bimap g h (a, b) = (g a, h b)

-- $ Symmetric Monoidal Functions
swap :: (a, b) -> (b, a)
swap (a, b) = (b, a)

assoc :: (a, (b, c)) -> ((a, b), c)
assoc (a, (b, c)) = ((a, b), c)

unitl :: a -> ((), a)
unitl a = ((), a)

unitr :: a -> (a, ())
unitr a = (a, ())

double :: a -> (a, a)
double a = (a, a)

newtype ListPair a b = LP { unLp :: [(a, b)]} deriving (Eq, Show)

-- $ contravariant functor instance
instance Functor (ListPair a) where
  fmap f = LP . fmap (bimap id f) . unLp


{- $ SUMS $-}

-- dualized definition of product.
-- defines a mapping-out property
-- from the terminal object in a category

-- for x, y in Cat C.
-- A coproduct, x + y,
-- together with morphisms:
-- i1 : x -> x + y
-- i2 : y -> x + y
-- such that for any object a and morphisms
-- f : x -> a and g : y -> a,
-- there is a unique morphism h : x + y -> a
-- such that the mapping-in diagram commutes
-- i1 x = x + y
-- i2 y = x + y
-- h (x + y) = a
-- f x = a & g y = a

data Coproduct a b = I1 a | I2 b

--data Either a b = Left a | Right b

either :: (a -> c) -> (b -> c) -> (Either a b -> c)
either f g (Left a) = f a
either f g (Right b) = g b

unEither :: (Either a b -> c) -> (a -> c, b -> c)
unEither h = (h . Left, h . Right)


instance Bifunctor Either where
  bimap f g (Left a) = Left . f $ a
  bimap f g (Right a) = Right . g $ a

-- A category is cocartesian if it has an initial object
-- and every pair of objects has a coproduct

-- A category is bicartesian if it is both cartesian
-- and cocartesian


{-$ DISTRIBUTIVITY $-}
-- isomorphism between the following types
-- Either (a, c) (b, c) -> ((Either a b), c)

distRL :: Either (a, c) (b, c) -> ((Either a b), c)
distRL (Left (a, c)) = (Left a, c)
distRL (Right (b, c)) = (Right b , c)


distLR :: ((Either a b), c) -> Either (a, c) (b, c)
distLR ((Left a), c) = Left (a, c)
distLR ((Right b), c) = Right (b, c)

{-$ EXPONENTIALS AND CURRYING $-}
