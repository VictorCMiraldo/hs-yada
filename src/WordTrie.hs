
module WordTrie where

import qualified Data.Map as M
import Data.Word (Word8)
import Data.Bits

data WordTrie a
  = Fork (Maybe a) (M.Map Word8 (WordTrie a))
  deriving (Eq , Show)

trieEmpty :: WordTrie a
trieEmpty = Fork Nothing M.empty

-- |Adds an element to our WordTrie set
trieAdd :: a -> (a -> a) -> [Word8] -> WordTrie a -> WordTrie a
trieAdd a0 incr []     (Fork ctr m) = Fork (maybe (Just a0) (Just . incr) ctr) m
trieAdd a0 incr (h:hs) (Fork ctr m) = Fork ctr $ M.alter go h m
  where
    go Nothing  = Just $ trieAdd a0 incr hs trieEmpty
    go (Just t) = Just $ trieAdd a0 incr hs t

-- |Looks up a value in a trie
trieLkup :: [Word8] -> WordTrie a -> Maybe a
trieLkup []     (Fork ctr m) = ctr
trieLkup (h:hs) (Fork ctr m) = M.lookup h m >>= trieLkup hs

-- |Zips a wordtrie
trieZipWith :: (a -> b -> c) -> WordTrie a -> WordTrie b -> WordTrie c
trieZipWith f (Fork ca m) (Fork cb n)
  = Fork (f <$> ca <*> cb) (M.intersectionWith (trieZipWith f) m n)


-- |Gets the octets in an Int; this is platform independent.
octets :: Int -> [Word8]
octets w
  = let nbits = finiteBitSize w
        nocts = nbits `div` 8
     in map fromIntegral
      $ [ w `shiftR` (8 * i) | i <- [nocts - 1 , nocts - 2 .. 0] ]

---------
-- Int specific stuff

trieAddInt :: Int -> WordTrie Int -> WordTrie Int
trieAddInt k = trieAdd 1 (+1) (octets k)


t1 :: WordTrie Word8
t1 = foldr (trieAdd 1 (+1)) trieEmpty
   . map (octets . (+123515))
   $ [1..40] ++ [12 .. 25]

t2 :: WordTrie Word8
t2 = foldr (trieAdd 1 (+1)) trieEmpty
   . (++ (map (octets . (+15235)) [1..100]))
   . map (octets . (+123515))
   $ [1..20]
