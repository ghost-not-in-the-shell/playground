{-# LANGUAGE MultiParamTypeClasses #-}
module PriorityQueue where

class Ord k => PriorityQueue q k v where
  empty     :: q k v
  insert    :: k -> v -> q k v -> q k v
  getMin    :: q k v -> Maybe v
  deleteMin :: q k v -> Maybe (q k v)
