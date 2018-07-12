{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Tree23_hashset where

import Control.Arrow ((***),(&&&))
import Data.Hashable
import Control.Applicative
import Control.Monad
import Control.Monad.State

import Tree23
import WordTrie
import Generics.MRSOP.Base
import Generics.MRSOP.Opaque
import Generics.MRSOP.Util hiding (Cons , Nil)
import Generics.MRSOP.Treefix

-- |I'll keep a set that counts how many times each common subtree
--  still shows up (and the path to it) in the source and destination.
--
--  In fact, at the beginning of the algorithm; this map contains
--  the possible syncpoints.
type Path = [Int]
type DiffM = State (WordTrie ([Path] , [Path]))

-- |Constructs a trie from a tree;
--  there are MUCH more efficient ways of doing this, btw!
--  For instance, do it bottom-up and re-use the preconputed hashes
trieFromTree :: Tree23 -> WordTrie [Path]
trieFromTree = go trieEmpty . (:[]) . ([],)
  where
    go :: WordTrie [Path] -> [(Path , Tree23)] -> WordTrie [Path]
    go tr []        = tr
    go tr ((_ , Leaf):ts) = go tr ts
    go tr ((h , t):ts)    = go (trieAdd [h] (h:) (octets $ hash t) tr)
                               (ts ++ map ((:h) *** id) (zip [0..] $ children t))

-- |Again; we can keep the hashes around for a much more efficient
--  version of this. Instead of Tree23; use Auth Tree23
trieTreeLkup :: Tree23 -> WordTrie a -> Maybe a
trieTreeLkup t = trieLkup (octets $ hash t)

-- |given two trees, compute the tries of all of their subtrees and
--  get their intersection
preprocess :: Tree23 -> Tree23 -> WordTrie ([Path] , [Path])
preprocess t1 t2 = trieZipWith (,) (trieFromTree t1) (trieFromTree t2)

-- |Extract a tree given a path
treeExtract :: Path -> Tree23 -> Maybe Tree23
treeExtract []     t = return t
treeExtract (p:ps) t
  = let c = children t
     in if p >= length c
        then Nothing
        else treeExtract ps (c !! p)
           
-- PROPERTY:
--
--  \all (ps , qs) \in img (preprocess t1 t2)
--    . map (flip treeExtract t1) ps =~= map (flip treeExtract t2) qs
--
--  l1 =~= l2 iff l1 ++ l2 == replicate n x for some n and x

mt1 , mt2 , mt3 , mt4 :: Tree23
mt1 = Node2 10 Leaf Leaf
mt2 = Node3 20 Leaf mt1 Leaf
mt3 = Node2 30 Leaf Leaf
mt4 = Node3 50 mt1 mt2 mt3


-- PROBLEM:
--
-- I want to define the following function:
--
-- getCtx :: (syncs : WordTrie ([Path] , [Path]))
--        -> Tx Singl FamTree23 CodesTree23 (Idx Tree23) (getAllSyncs syncs)
--
-- In fact; we only know the type of the Treefix at run-time. Hence,
-- we pack it in an existential
data TxE :: (kon -> *) -> [*] -> [[[Atom kon]]] -> Nat -> * where
  TxE :: Tx ki fam codes i js -> TxE ki fam codes i

getCtx :: WordTrie ([Path] , [Path]) -> Tree23
       -> TxE Singl FamTree23 CodesTree23 Z
getCtx wd tr
  = case trieTreeLkup tr wd of
      -- Recurse down the children of tr
      Nothing        -> _
      Just (ps , qs) -> _

{-
  
hdiff :: (Alternative m) => Tree23 -> Tree23 -> m Patch
hdiff t1 t2 = evalState (hdiff' 0 t1 0 t2) (preprocess t1 t2)
            

hdiff' :: (Alternative m)
       => Int -> Tree23 -> Int -> Tree23 -> DiffM (m Patch)
hdiff' t1 t2 = undefined
-}
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
