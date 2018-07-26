{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
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
import Data.Type.Equality
import Data.Maybe (mapMaybe)
import qualified Data.List as L
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

enumNP :: NP f xs -> [NS f xs]
enumNP NP0 = []
enumNP (fx :* fxs) = Here fx : map There (enumNP fxs)

trieFromTree :: Tree23 -> WordTrie [MyPath]
trieFromTree t = go trieEmpty [(id , t)]
  where
    -- CPS style for constructing paths
    go :: WordTrie [MyPath] -> [(MyPath -> MyPath , Tree23)] -> WordTrie [MyPath]
    go tr []        = tr
    go tr ((_ , Leaf):ts) = go tr ts
    go tr ((h , t):ts) = case sop (sfrom $ into @FamTree23 t) of
      Tag c ps -> go (trieAdd [h HoleW] (h HoleW :) (octets $ hash t) tr)
                     (ts ++ mapMaybe (goNS h c) (enumNP ps))

    isRec :: NA Singl (El FamTree23) ix -> Maybe Tree23
    isRec (NA_I x) 
      = case getElSNat x of
          SZ -> return $ unEl x
    isRec _
      = Nothing

    constP :: MyPath -> NA Singl (El FamTree23) a -> Way CodesTree23 a
    constP p (NA_I el)
      = case getElSNat el of
          SZ -> p
    constP _ _        = error "constP"

    -- The goNS function returns whatever tree was selected in the inj
    -- into NS and returns the continuation by adding the hole at
    -- that same injection.
    goNS :: IsNat c
         => (MyPath -> MyPath) -> Constr (Lkup Z CodesTree23) c
         -> NS (NA Singl (El FamTree23)) (Lkup c (Lkup Z (CodesTree23)))
         -> Maybe (MyPath -> MyPath , Tree23)
    goNS h c ns = do t   <- elimNS isRec ns
                     return ( h . Follow c . (\p -> mapNS (constP p) ns)
                            , t)

-- |Again; we can keep the hashes around for a much more efficient
--  version of this. Instead of Tree23; use Auth Tree23
trieTreeLkup :: Tree23 -> WordTrie a -> Maybe a
trieTreeLkup t = trieLkup (octets $ hash t)

-- |given two trees, compute the tries of all of their subtrees and
--  get their intersection
preprocess :: Tree23 -> Tree23 -> WordTrie ([MyPath] , [MyPath])
preprocess t1 t2 = trieZipWith (,) (trieFromTree t1) (trieFromTree t2)

data UTx :: (kon -> *) -> [*] -> [[[Atom kon]]] -> Nat -> * -> *  where
  UTxHere :: x -> UTx ki fam codes i x
  UTxPeel :: (IsNat n) => Constr (Lkup i codes) n
         -> UTxNP ki fam codes (Lkup n (Lkup i codes)) x
         -> UTx ki fam codes i x

data UTxNP :: (kon -> *) -> [*] -> [[[Atom kon]]] -> [Atom kon] -> * -> *
    where
  UTxNPNil   :: UTxNP ki fam codes '[] x
  UTxNPPath  :: (IsNat i)
            => UTx ki fam codes i x
            -> UTxNP ki fam codes prod x
            -> UTxNP ki fam codes (I i ': prod) x
  UTxNPSolid :: ki k
            -> UTxNP ki fam codes prod x
            -> UTxNP ki fam codes (K k ': prod) x

utxGetX :: UTx ki fam codes i x -> [x]
utxGetX utx = go utx []
  where 
    go :: UTx ki fam codes i x -> ([x] -> [x])
    go (UTxHere x) = (x:)
    go (UTxPeel _ xs)  = utxnpGetX xs

    utxnpGetX :: UTxNP ki fam codes prod x -> ([x] -> [x])
    utxnpGetX UTxNPNil = id
    utxnpGetX (UTxNPSolid _ ps) = utxnpGetX ps
    utxnpGetX (UTxNPPath i ps) = go i . utxnpGetX ps 

deriving instance (Show1 ki , Show x) => Show (UTx ki fam codes i x)
instance (Show1 ki , Show x) => Show (UTxNP ki fam codes prod x) where
  show UTxNPNil = "Nil"
  show (UTxNPPath p ps) = "(" ++ show p ++ ") :* " ++ show ps
  show (UTxNPSolid ki ps) = show1 ki ++ " :* " ++ show ps

data DiffState = DiffState 
  { sharingMap :: WordTrie ([MyPath] , [MyPath])
  , seenMap    :: WordTrie Int
  , fresh      :: Int
  }
type DiffM = State DiffState

-- The Int is used to "number" the hole. All holes with
-- number "n" must be contracted in the source and
-- map to holes with number "n" in the dest.
type MyTreefix = UTx Singl FamTree23 CodesTree23 Z Int
type MyTreefixNP prod = UTxNP Singl FamTree23 CodesTree23 prod Int

issueHoleFor :: Tree23 -> DiffM MyTreefix
issueHoleFor tr
  = do res <- (trieTreeLkup tr . seenMap) <$> get
       case res of
         Just i -> return (UTxHere i)
         Nothing -> do
           i <- fresh <$> get
           modify (\st -> st { seenMap = trieAdd i (const i) (octets $ hash tr) (seenMap st)
                             , fresh   = i + 1
                             })
           return (UTxHere i)

traverseConstr :: Tree23 -> DiffM MyTreefix
traverseConstr tr
  = case sop (sfrom $ into @FamTree23 tr) of
      Tag ctr ptr -> UTxPeel ctr <$> go ptr
  where
    go :: PoA Singl (El FamTree23) prod
       -> DiffM (MyTreefixNP prod)
    go NP0 = return UTxNPNil
    go (NA_K ki :* rest) = UTxNPSolid ki <$> go rest
    go (NA_I vi :* rest)
      = case getElSNat vi of
          SZ -> UTxNPPath <$> getPathE (unEl vi)
                          <*> go rest

getPathE :: Tree23 -> DiffM MyTreefix
getPathE tr
  = do res <- (trieTreeLkup tr . sharingMap) <$> get
       case res of
         Nothing           -> traverseConstr tr
         Just (others , _) -> issueHoleFor tr

runDiffMWithSharing :: WordTrie ([MyPath] , [MyPath])
                    -> DiffM a -> a
runDiffMWithSharing sharing dm
  = evalState dm (DiffState sharing trieEmpty 0)

experiment :: Tree23 -> Tree23 -> (MyTreefix , MyTreefix)
experiment t u
  = let sharing = preprocess t u
     in runDiffMWithSharing sharing $
       do del <- getPathE t
          ins <- getPathE u
          -- Now, we might be computing something with too much sharing.
          -- We must go over the holes in both UTx's and
          -- remove those that do not appear in the other place
          -- by replacing them with a tree.
          -- let keysD = L.nub $ utxGetX del
          -- let keysI = L.nub $ utxGetX ins
          -- let del' = replaceHoles (keysD L.\\ keysI) t del
          -- let ins' = replaceHoles (keysI L.\\ keysD) u ins
          -- return (del' , ins')
          return (del , ins)

makeSolidTx :: Tree23 -> MyTreefix
makeSolidTx t
  = case sop (sfrom $ into @FamTree23 t) of
      Tag c p -> UTxPeel c (go p)
  where
    go :: PoA Singl (El FamTree23) prod
       -> MyTreefixNP prod
    go NP0 = UTxNPNil
    go (NA_K ki :* rest) = UTxNPSolid ki (go rest)
    go (NA_I vi :* rest)
      = case getElSNat vi of
          SZ -> UTxNPPath (makeSolidTx (unEl vi)) (go rest)

replaceHoles :: [Int] -> Tree23 -> MyTreefix -> MyTreefix
replaceHoles [] _ = id
replaceHoles xs t = replaceHoles' xs t

-- predondition: the treefix is a valid treefix for t
replaceHoles' :: [Int] -> Tree23 -> MyTreefix -> MyTreefix
replaceHoles' ks t (UTxHere x)
  | x `elem` ks = makeSolidTx t
  | otherwise   = UTxHere x
replaceHoles' ks t (UTxPeel c1 txnp)
  = case sop (sfrom $ into @FamTree23 t) of
      Tag c2 p -> case testEquality c1 c2 of
        Nothing   -> error "precondition failure"
        Just Refl -> UTxPeel c1 (replaceHolesNP ks p txnp)
  where
    replaceHolesNP :: [Int] -> PoA Singl (El FamTree23) prod
                   -> MyTreefixNP prod
                   -> MyTreefixNP prod
    replaceHolesNP ks NP0 _ = UTxNPNil
    replaceHolesNP ks (_ :* as) (UTxNPSolid ki rest)
      = UTxNPSolid ki $ replaceHolesNP ks as rest
    replaceHolesNP ks (NA_I a :* as) (UTxNPPath i rest)
      = case getElSNat a of
         SZ -> UTxNPPath (replaceHoles' ks (unEl a) i) (replaceHolesNP ks as rest)

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
