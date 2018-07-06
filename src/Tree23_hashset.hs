{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
{-# ScopedTypeVariables #-}
module Tree23_hashset where

import Data.Hashable
import Control.Applicative
import Control.Monad
import Control.Monad.State

import Tree23
import WordTrie

-- |I'll keep a set that counts how many times each common subtree
--  still shows up (and at which height) in the source and destination.
--
--  In fact, at the beginning of the algorithm; this map contains
--  the possible syncpoints.
type DiffM = State (WordTrie ([Int] , [Int]))

-- |Constructs a trie from a tree;
--  there are MUCH more efficient ways of doing this, btw!
--  For instance, do it bottom-up and re-use the preconputed hashes
trieFromTree :: Tree23 -> WordTrie [Int]
trieFromTree = go trieEmpty . (:[]) . (0,)
  where
    go :: WordTrie [Int] -> [(Int , Tree23)] -> WordTrie [Int]
    go tr []        = tr
    go tr ((_ , Leaf):ts) = go tr ts
    go tr ((h , t):ts)    = go (trieAdd [h] (h:) (octets $ hash t) tr)
                               (ts ++ map (h+1,) (children t))

-- |Again; we can keep the hashes around for a much more efficient
--  version of this. Instead of Tree23; use Auth Tree23
trieTreeLkup :: Tree23 -> WordTrie a -> Maybe a
trieTreeLkup t = trieLkup (octets $ hash t)

-- |given two trees, compute the tries of all of their subtrees and
--  get their intersection
preprocess :: Tree23 -> Tree23 -> WordTrie ([Int] , [Int])
preprocess t1 t2 = trieZipWith (,) (trieFromTree t1) (trieFromTree t2)


mt1 , mt2 , mt3 , mt4 :: Tree23
mt1 = Node2 10 Leaf Leaf
mt2 = Node3 20 Leaf mt1 Leaf
mt3 = Node2 30 Leaf Leaf
mt4 = Node3 50 mt1 mt2 mt3
  
hdiff :: (Alternative m) => Tree23 -> Tree23 -> m Patch
hdiff t1 t2 = evalState (hdiff' 0 t1 0 t2) (preprocess t1 t2)
            

hdiff' :: (Alternative m)
       => Int -> Tree23 -> Int -> Tree23 -> DiffM (m Patch)
hdiff' t1 t2 = undefined
{-
hdiff' t1 t2 = (trieTreeLkup t1 <$> get) >>= ponderDel
  where
    ponderDel :: (Alternative m) => Maybe (Int , Int) -> DiffM (m Patch)
    -- t1 does not appear as a common subtree; this
    -- forces it to be deleted.
    ponderDel Nothing
      = (<|>) <$> doDel t1 t2
              <*> (trieTreeLkup t2 <$> get >>= ponderIns)
    -- t1 appears i times in the source and j times in
    -- the destination.
    ponderDel (Just (i , j))
      | i > j     = (<|>) <$> doDel t1 t2 <*> doCpy t1 t2
      | otherwise = doCpy t1 t2

    ponderIns :: (Alternative m) => Maybe (Int , Int) -> DiffM (m Patch)
    ponderIns Nothing = undefined
    ponderIns _ = undefined

    doDel :: (Alternative m) => Tree23 -> Tree23 -> DiffM (m Patch)
    doDel t1 t2 = _

    doCpy ::  (Alternative m) => Tree23 -> Tree23 -> DiffM (m Patch)
    doCpy t1 t2 = _
-}
