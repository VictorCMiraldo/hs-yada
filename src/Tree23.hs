{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Tree23 where

import GHC.Generics hiding (S)

import Data.Function (on)
import Data.List (sortBy , groupBy)

import Data.Hashable

import Control.Applicative
import Control.Monad

-- These are all necessary to use the template haskell
-- functionality; together with:
--   {-# LANGUAGE PatternSynonyms MultiParamTypeClasses TemplateHaskell #-}
--
import Generics.MRSOP.Base
import Generics.MRSOP.Util hiding (All, Nil, Cons)
import Generics.MRSOP.Opaque
import Generics.MRSOP.TH

-- |2-3-Trees declaration
data Tree23
  = Node2 Int Tree23 Tree23
  | Node3 Int Tree23 Tree23 Tree23
  | Leaf
  deriving (Eq , Show , Generic)

deriveFamily [t| Tree23 |]

instance Hashable Tree23

children :: Tree23 -> [Tree23]
children Leaf = []
children (Node2 _ l r) = [l , r]
children (Node3 _ a b c) = [a,b,c]

-- |Contexts over 2-3-Trees
data Ctx
  = Hole
  | CNode2_0 Int Tree23 Ctx
  | CNode2_1 Int Tree23 Ctx
  | CNode3_0 Int Tree23 Tree23 Ctx
  | CNode3_1 Int Tree23 Tree23 Ctx
  | CNode3_2 Int Tree23 Tree23 Ctx
  deriving (Eq , Show)

-- |Enumerate all possible contexts
ctxEnum :: (MonadPlus m) => Tree23 -> m (Ctx , Tree23)
ctxEnum Leaf = return (Hole , Leaf)
ctxEnum t@(Node2 i t0 t1)
  =   return (Hole , t)
  <|> ((CNode2_0 i t1 *** id) <$> ctxEnum t0)
  <|> ((CNode2_1 i t0 *** id) <$> ctxEnum t1)                     
ctxEnum t@(Node3 i t0 t1 t2)
  =   return (Hole , t)
  <|> ((CNode3_0 i t1 t2 *** id) <$> ctxEnum t0)
  <|> ((CNode3_1 i t0 t2 *** id) <$> ctxEnum t1)                     
  <|> ((CNode3_2 i t0 t1 *** id) <$> ctxEnum t2)                     

-- |Plugs a context into a tree.
ctxPlug :: Ctx -> Tree23 -> Tree23
ctxPlug Hole t = t
ctxPlug (CNode2_0 i t1 c) t    = Node2 i (ctxPlug c t) t1 
ctxPlug (CNode2_1 i t0 c) t    = Node2 i t0 (ctxPlug c t)
ctxPlug (CNode3_0 i t1 t2 c) t = Node3 i (ctxPlug c t) t1 t2
ctxPlug (CNode3_1 i t0 t2 c) t = Node3 i t0 (ctxPlug c t) t2
ctxPlug (CNode3_2 i t0 t1 c) t = Node3 i t0 t1 (ctxPlug c t)

-- |Spinees over 2-3-Trees
data Spine :: * -> * where
  Scp       :: Spine t
  Set       :: Int -> Int -> Spine Int
  ScnsNode2 :: Spine Int -> Spine Tree23 -> Spine Tree23 -> Spine Tree23
  ScnsNode3 :: Spine Int -> Spine Tree23 -> Spine Tree23 -> Spine Tree23 -> Spine Tree23
  SchgN2N3  :: Spine Int -> Al (S (S Z)) (S (S (S Z))) -> Spine Tree23
  SchgN3N2  :: Spine Int -> Al (S (S (S Z))) (S (S Z)) -> Spine Tree23
  -- Leaves becomming node 2 or node 3 is just cold 'set'
  SchgLN2   :: Int -> Tree23 -> Tree23 -> Spine Tree23
  SchgLN3   :: Int -> Tree23 -> Tree23 -> Tree23 -> Spine Tree23
  SchgN2L   :: Int -> Tree23 -> Tree23 -> Spine Tree23
  SchgN3L   :: Int -> Tree23 -> Tree23 -> Tree23 -> Spine Tree23

deriving instance (Show x) => Show (Spine x)
deriving instance (Eq x) => Eq (Spine x)

-- |Alignments mixed with fixpoints already
data Al :: Nat -> Nat -> * where
  A0   :: Al Z Z
  AIns :: Tree23 -> Al i j -> Al i (S j)
  ADel :: Tree23 -> Al i j -> Al (S i) j
  AMod :: Ctx -> Ctx -> Spine Tree23 -> Al i j -> Al (S i) (S j)

deriving instance Show (Al i j)
deriving instance Eq (Al i j)

countMods :: Al i j -> Int
countMods A0 = 0
countMods (AIns _ a) = countMods a
countMods (ADel _ a) = countMods a
countMods (AMod _ _ _ a) = 1 + countMods a

data All :: Nat -> * where
  Nil  :: All Z
  Cons :: Tree23 -> All i -> All (S i)

allLength :: All i -> Int
allLength Nil         = 0
allLength (Cons _ xs) = 1 + allLength xs

als :: (MonadPlus m) => All i -> All j -> m (Al i j)
als xs ys = let lx = allLength xs
                ly = allLength ys
             in do al <- als' xs ys
                   guard (countMods al == min lx ly)
                   return al

-- unguarded
als' :: (MonadPlus m) => All i -> All j -> m (Al i j)
als' Nil Nil = return A0
als' (Cons x xs) Nil = ADel x <$> als xs Nil
als' Nil (Cons x xs) = AIns x <$> als Nil xs
als' (Cons x xs) (Cons y ys)
  =   (AIns y <$> als (Cons x xs) ys)
  <|> (ADel x <$> als xs (Cons y ys))
  <|> (do (cx , x') <- ctxEnum x
          (cy , y') <- ctxEnum y
          guard (ctxCompat cx cy)
          AMod cx cy <$> spine x' y' <*> als xs ys
      )

-- |Computes the spine between two trees; a spine captures changes in
--  content.
spine :: (MonadPlus m) => Tree23 -> Tree23 -> m (Spine Tree23)    
spine x y
  | x == y    = return Scp
  | otherwise = go x y
  where

    go (Node3 i t0 t1 t2) (Node3 j u0 u1 u2)
      = ScnsNode3 (Set i j) <$> spine t0 u0 <*> spine t1 u1 <*> spine t2 u2
    go (Node2 i t0 t1)    (Node2 j u0 u1)
      = ScnsNode2 (Set i j) <$> spine t1 u0 <*> spine t1 u1

    go (Node2 i t0 t1) (Node3 j u0 u1 u2)
      = SchgN2N3 (Set i j) <$> als (Cons t0 (Cons t1 Nil))
                                   (Cons u0 (Cons u1 (Cons u2 Nil)))

    go (Node3 i t0 t1 t2) (Node2 j u0 u1)
      = SchgN3N2 (Set i j) <$> als (Cons t0 (Cons t1 (Cons t2 Nil)))
                                   (Cons u0 (Cons u1 Nil))

    go Leaf (Node2 j u0 u1)    = return $ SchgLN2 j u0 u1
    go (Node2 i t0 t1) Leaf    = return $ SchgN2L i t0 t1
    go Leaf (Node3 j u0 u1 u2) = return $ SchgLN3 j u0 u1 u2
    go (Node3 j t0 t1 t2) Leaf = return $ SchgN3L j t0 t1 t2

    go x y = error $ show x ++ ";" ++ show y

type Patch = Al (S Z) (S Z)

diff :: (MonadPlus m) => Tree23 -> Tree23 -> m Patch
diff x y
  = do (cx , x') <- ctxEnum x
       (cy , y') <- ctxEnum y
       guard (ctxCompat cx cy)
       AMod cx cy <$> spine x' y' <*> return A0

-- We say that contexts are compatible if we are not deleting and inserting
-- the very same constructor.
ctxCompat :: Ctx -> Ctx -> Bool
ctxCompat (CNode2_0 _ _ _)   (CNode2_0 _ _ _)   = False
ctxCompat (CNode2_1 _ _ _)   (CNode2_1 _ _ _)   = False
ctxCompat (CNode3_0 _ _ _ _) (CNode3_0 _ _ _ _) = False
ctxCompat (CNode3_1 _ _ _ _) (CNode3_1 _ _ _ _) = False
ctxCompat (CNode3_2 _ _ _ _) (CNode3_2 _ _ _ _) = False
ctxCompat _                  _                  = True

---------------------------
-- * Height of a Patch * --

spineHeight :: Spine x -> Int
spineHeight (Scp       )        = 0
spineHeight (Set       x y)
  | x == y    = 0
  | otherwise = 1
spineHeight (ScnsNode2 _ a b)   = 1 + sum [spineHeight a , spineHeight b]
spineHeight (ScnsNode3 _ a b c) = 1 + sum [spineHeight a , spineHeight b , spineHeight c]
spineHeight (SchgN2N3  _ al)    = 1 + alHeight al
spineHeight (SchgN3N2  _ al)    = 1 + alHeight al
spineHeight (SchgLN2   _ a b)   = 1 + sum [treeHeight a , treeHeight b]
spineHeight (SchgLN3   _ a b c) = 1 + sum [treeHeight a , treeHeight b , treeHeight c]
spineHeight (SchgN2L   _ a b)   = 1 + sum [treeHeight a , treeHeight b]
spineHeight (SchgN3L   _ a b c) = 1 + sum [treeHeight a , treeHeight b , treeHeight c]
      
treeHeight :: Tree23 -> Int
treeHeight Leaf = 0
treeHeight (Node2 _ a b)   = 1 + (treeHeight a) + (treeHeight b)
treeHeight (Node3 _ a b c) = 1 + sum [treeHeight a , treeHeight b , treeHeight c]

alHeight :: Al i j -> Int
alHeight A0 = 0
alHeight (AIns t a) = 1 + (treeHeight t) + (alHeight a)
alHeight (ADel t a) = 1 + (treeHeight t) + (alHeight a)
alHeight (AMod cd ci s a)
  = 1 + sum [ 2*ctxHeight cd , 2*ctxHeight ci , spineHeight s , alHeight a]

ctxHeight :: Ctx -> Int
ctxHeight (Hole) = 0
ctxHeight (CNode2_0 _ t c)   = 1 + (treeHeight t) + (ctxHeight c)
ctxHeight (CNode2_1 _ t c)   = 1 + (treeHeight t) + (ctxHeight c)
ctxHeight (CNode3_0 _ t u c) = 1 + sum [treeHeight t , treeHeight u] + ctxHeight c
ctxHeight (CNode3_1 _ t u c) = 1 + sum [treeHeight t , treeHeight u] + ctxHeight c
ctxHeight (CNode3_2 _ t u c) = 1 + sum [treeHeight t , treeHeight u] + ctxHeight c

{-
spineHeight :: Int -> Spine x -> Int
spineHeight n (Scp       )        = 0
spineHeight n (Set       x y)
  | x == y    = 0
  | otherwise = 1
spineHeight n (ScnsNode2 _ a b)   = n + maximum [spineHeight (n+1) a , spineHeight (n+1) b]
spineHeight n (ScnsNode3 _ a b c) = n + maximum [spineHeight (n+1) a , spineHeight (n+1) b , spineHeight (n+1) c]
spineHeight n (SchgN2N3  _ al)    = n + alHeight (n+1) al
spineHeight n (SchgN3N2  _ al)    = n + alHeight (n+1) al
spineHeight n (SchgLN2   _ a b)   = n + maximum [treeHeight a , treeHeight b]
spineHeight n (SchgLN3   _ a b c) = n + maximum [treeHeight a , treeHeight b , treeHeight c]
spineHeight n (SchgN2L   _ a b)   = n + maximum [treeHeight a , treeHeight b]
spineHeight n (SchgN3L   _ a b c) = n + maximum [treeHeight a , treeHeight b , treeHeight c]
      
treeHeight :: Tree23 -> Int
treeHeight Leaf = 0
treeHeight (Node2 _ a b)   = 1 + max (treeHeight a) (treeHeight b)
treeHeight (Node3 _ a b c) = 1 + maximum [treeHeight a , treeHeight b , treeHeight c]

alHeight :: Int -> Al i j -> Int
alHeight n A0 = 0
alHeight n (AIns t a) = n + max (treeHeight t) (alHeight (n+1) a)
alHeight n (ADel t a) = n + max (treeHeight t) (alHeight (n+1) a)
alHeight n (AMod cd ci s a)
  = let ctxH = ctxHeight (n+1) cd + ctxHeight (n+1) ci
     in maximum [spineHeight ctxH s , alHeight (n+1) a]

ctxHeight :: Int -> Ctx -> Int
ctxHeight n (Hole) = 0
ctxHeight n (CNode2_0 _ t c)   = n + (treeHeight t) + (ctxHeight (n+1) c)
ctxHeight n (CNode2_1 _ t c)   = n + (treeHeight t) + (ctxHeight (n+1) c)
ctxHeight n (CNode3_0 _ t u c) = n + maximum [treeHeight t , treeHeight u] + ctxHeight (n+1) c
ctxHeight n (CNode3_1 _ t u c) = n + maximum [treeHeight t , treeHeight u] + ctxHeight (n+1) c
ctxHeight n (CNode3_2 _ t u c) = n + maximum [treeHeight t , treeHeight u] + ctxHeight (n+1) c
-}


instance Ord Patch where
  compare = compare `on` alHeight 

betterPatches :: [Patch] -> [Patch]
betterPatches = safeHead . groupBy ((==) `on` alHeight) . sortBy compare
  where
    safeHead [] = []
    safeHead (x:_) = x

bestDiffs :: Tree23 -> Tree23 -> [Patch]
bestDiffs x y = betterPatches (diff x y)
          
t1 , t2 , t3 :: Tree23
t1 = Node2 30 (Node2 60 Leaf Leaf) Leaf
t2 = Node2 30 (Node2 10 Leaf Leaf) Leaf
t3 = Node2 100 Leaf t1

test1 = (AMod (CNode2_1 100 Leaf Hole) Hole Scp A0) `elem` (bestDiffs t3 t1)

u1 , u2 :: Tree23
u1 = Node2 50 Leaf Leaf
u2 = Node2 60 Leaf Leaf

test2 = (AMod Hole Hole (ScnsNode2 (Set 50 60) Scp Scp) A0) `elem` (bestDiffs u1 u2)

v1 , v2 :: Tree23
v1 = Node3 100 (Node2 50 Leaf Leaf)
               (Node2 75 Leaf Leaf)
               (Node3 95 Leaf Leaf Leaf)
v2 = Node3 100 (Node3 50 Leaf Leaf Leaf)
               Leaf
               (Node3 95 Leaf Leaf Leaf)
     
