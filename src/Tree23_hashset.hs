{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Tree23_hashset where

import Control.Arrow ((***),(&&&))
import Data.Hashable
import Data.Maybe (mapMaybe)
import Control.Applicative
import Control.Monad
import Control.Monad.State

import Tree23 hiding (Hole)
import WordTrie
import Generics.MRSOP.Base
import Generics.MRSOP.Opaque
import Generics.MRSOP.Util hiding (Cons , Nil)
import Generics.MRSOP.Treefix

type MyPath = Way CodesTree23 (I Z)
type DiffM = State (WordTrie ([MyPath] , [MyPath]))

enumNP :: NP f xs -> [NS f xs]
enumNP NP0 = []
enumNP (fx :* fxs) = Here fx : map There (enumNP fxs)

trieFromTree :: Tree23 -> WordTrie [MyPath]
trieFromTree t = go trieEmpty [(HoleW , t)]
  where
    go :: WordTrie [MyPath] -> [(MyPath , Tree23)] -> WordTrie [MyPath]
    go tr []        = tr
    go tr ((_ , Leaf):ts) = go tr ts
{-
    go tr ((h , t):ts)    = go (trieAdd [h] (h:) (octets $ hash t) tr)
                               (ts ++ map (mergePath h *** id) (zip [0..] $ children t))
-}
    go tr ((h , t):ts) = case sop (sfrom $ into @FamTree23 t) of
      Tag c ps -> go (trieAdd [h] (h :) (octets $ hash t) tr)
                     (ts ++ mapMaybe (goNS _ c) (enumNP ps))

    

    isRec :: NA Singl (El FamTree23) ix -> Maybe Tree23
    isRec = _

    constHole :: NA Singl (El FamTree23) a -> Maybe (Way CodesTree23 a)
    constHole (NA_I _) = return HoleW
    constHole _        = Nothing

    goNS :: IsNat c
         => (MyPath -> MyPath) -> Constr (Lkup Z CodesTree23) c
         -> NS (NA Singl (El FamTree23)) (Lkup c (Lkup Z (CodesTree23)))
         -> Maybe (MyPath , Tree23)
    goNS h c ns = do aux <- mapNSM constHole ns
                     t   <- elimNS isRec ns
                     return (h (Follow c aux) , t)
{-
    isRec uptohere (There rest) = isRec uptohere rest
    isRec uptohere (Here  (NA_K _))  = Nothing
    isRec uptohere (Here  (NA_I el))
      = case getElSNat el of
          SZ -> Just (HoleW , unEl el)
 
    mergePath :: MyPath -> Integer -> MyPath
    mergePath p i = _

-}
{-
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
-}
mt1 , mt2 , mt3 , mt4 :: Tree23
mt1 = Node2 10 Leaf Leaf
mt2 = Node3 20 Leaf mt1 Leaf
mt3 = Node2 30 Leaf Leaf
mt4 = Node3 50 mt1 mt2 mt3

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
