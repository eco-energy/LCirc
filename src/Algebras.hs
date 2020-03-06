{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}
module Algebras where

import Prelude hiding ((.))
import Data.Void
import Data.Maybe
import ConCat.Pair
import ConCat.Category
import CatUtils
import qualified Data.Text as Text
import Data.Text (Text(..))
-- Two parts to an algebra:
-- 1) creation of expression
-- 2) evaluation

-- An expression is a tree whose nodes are operators and whose leaves are either constants or value placeholders
-- It is defined as a recursive data structure
data Expr = Plus  Expr Expr
          | Times Expr Expr
          | Const Double
          | Var   String

expr :: Expr
expr = Plus (Times (Const 2)
                   (Times (Var "x") (Var "x")))
            (Plus (Times (Const 3) (Var "x"))
                  (Const 4))

-- recursive process of constructing expressions can be decomposed into non-recursive steps.
-- Non-recursive type constructor with a placeholder for recursive bits

data ExprF a = PlusF  a a
             | TimesF a a
             | ConstF a
             | VarF   String
             deriving (Eq, Show)

type Leaf = ExprF Void
{--
-- TODO: To Doc Tests

-- Leaves can clearly only be constants or variables
e3, ex :: Leaf
e3 = ConstF 3
ex = VarF "x"

-- kinda like binOp?
type Expr2 = ExprF Leaf
e3x, ex2, e2 :: Expr2
e3x = TimesF e3 ex
e4 = ConstF 4
ex2 = TimesF ex ex
e2 = ConstF 2

type Expr3 = ExprF Expr2
type Expr4 = ExprF Expr3
e3xp4, e2x2 :: Expr3
e3xp4 = PlusF e3x e4
e2x2 = TimesF e2 ex2
expr' :: Expr4
expr' = PlusF e2x2 e3xp4
--}

-- If we apply ExprF infinitely manu times, we should get a data type that can deal with any depth tree.
-- We can actually get a typeconstructor isomorphic to the original recursive defintion of Expr.
-- But the type constructor we're iterating must be a Functor

instance Functor ExprF where
  fmap f (PlusF a a') = PlusF (f a) (f a')
  fmap f (TimesF a a') = TimesF (f a) (f a')
  fmap f (ConstF c) = ConstF $ f c
  fmap f (VarF v) = VarF v

-- Evaluation of expressions is the second component of an algebra.
-- Here we use it to evaluate a Tree to a double
eval :: (Num a) => ExprF a -> Maybe a
eval (ConstF a) = Just a
eval (VarF "x") = Just 2
eval (VarF _) = Nothing
eval (PlusF x y) = Just (x + y)
eval (TimesF x y) = Just $ x * y

tshow :: (Show a) => a -> Text
tshow = Text.pack . show

showEx :: ExprF Text -> Text
showEx (ConstF a) = "const: " <> (tshow a)
showEx (VarF a) = "var: " <> (tshow a)
showEx (PlusF x y) = Text.intercalate " + " [tshow x, tshow y]
showEx (TimesF x y) = Text.intercalate " * " [tshow x, tshow y]

-- How we combine partial evaluators into one recursive algorithm that would evaluate any recursive expression tree.


{--$ The Algebra $--}

-- An Endofunctor F.
-- In more categorical settings this must still be an endofunctor rather than
-- a functor between categories, because we have to be able to recursively apply it ti itself.


endoF :: (Bifunctor k) => (a -> a') -> (b -> b') ->  k a b -> k a' b'
endoF f g = bimap f g
-- Evaluators for this functor are called F-algebras
-- Here we chose a
            --  type a :: Double
            --  morphism :: F a -> a
  -- A different type would have required a
  -- different morphism


instance Foldable ExprF where
  -- foldMap (a -> m) -> t a -> m
  foldMap = undefined --fmap f t
  --foldMap f (x:xs) = eval x 


{------------------------------------------
             Algebras
------------------------------------------}

-- F-algebra (c, phi)
-- Let F : C -> C be a functor.
-- (a) An object c in C called the carrier
-- a morphism phi :: F c -> c called the structure map

-- Given two F-algebras (c, phi) and (d, gam),
-- a morphism f: (c, phi) -> (d, gam) is =>
-- a morphism f : c -> d in C such that
-- the following laws must hold
-- f :: c = d
-- phi $ F c = c
-- gam $ F d = d
-- (F f) (F c) = F d

-- $ There is a category F-Alg, whose objects are
-- F-algebras, morphisms are morphisms of F-algebras,
-- and whose composition and identities
-- are given by that in C.











{--------------------------------------------------------------------
                   Utilities
--------------------------------------------------------------------}
maybesToList = (map isJust) . (filter isNothing)

