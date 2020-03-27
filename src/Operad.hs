{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Operad where

import Data.Monoid
import Control.Monad.Writer
import Control.Monad.State


data Tree a = Leaf a | Branch [Tree a] deriving (Eq, Show)

-- If we want to apply a function to every element of the tree,
-- we use:

instance Functor Tree where
  fmap f (Leaf x) = Leaf $ f x
  fmap f (Branch ts) = Branch $ map (fmap f) ts


-- ZipTree
instance Applicative Tree where
  -- a -> f a
  pure = Leaf
  -- <*> :: f (a -> b) -> f a -> f b
  (Leaf f) <*> (Leaf x) = Leaf (f x)
  (Branch []) <*> (Branch _) = Branch []
  (Branch _) <*> (Branch []) = Branch []
  (Branch fs) <*> (Branch xs) = Branch $ map apl fx
    where
      --fx :: [(Tree (a -> b), a)]
      apl (Leaf f, x) = fmap f x
      apl (bf@(Branch fs), x) = bf <*> x
      --apl (Branch [], x) = undefined 
      fx = zip fs xs


-- We can also apply monadic functions by constructing
class FunctorM c where
  fmapM :: Monad m => (a -> m b) -> c a -> m (c b)

instance FunctorM Tree where
  fmapM f (Leaf x) = do
    y <- f x
    return (Leaf y)
  fmapM f (Branch ts) = do
    ts' <- mapM (fmapM f) ts
    return (Branch ts')



class Operad a where
  degree :: a -> Int
  identity :: a
  o :: a -> [a] -> a


-- What would a Tree monad look like?

instance Monad Tree where
  -- m a -> (a -> m b) -> m b
  return = pure
  (Leaf a) >>= f = f a
  (Branch ts) >>= f = joinTree $ Branch $ map (f <$>) ts
    where
      --f :: Tree (a -> b) -> (a -> Tree b)
      -- f (a -> b) -> f a -> f b
      -- (a -> m b) -> f a -> f b
      flap ff x = (\f -> f x) <$> ff


joinTree :: Tree (Tree a) -> Tree a
joinTree (Leaf a) = a
joinTree (Branch []) = Branch $ []
--joinTree (Branch ((Leaf x):xs)) = Branch $ x:xs
--joinTree (Branch ((Branch x):xs)) = map joinTree x
