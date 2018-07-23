{-# LANGUAGE MultiParamTypeClasses #-}
module FiniteMap where

class Ord k => FiniteMap s k v where
  empty  :: s k v
  insert :: k -> v -> s k v -> s k v
  lookup :: k -> s k v -> Maybe v
