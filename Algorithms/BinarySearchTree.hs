{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, NoImplicitPrelude, UnicodeSyntax #-}
module BinarySearchTree where
import FiniteMap
import Prelude hiding (lookup)

data Tree k v
  = Leaf
  | Node k v (Tree k v) (Tree k v)
  deriving (Show)

instance Ord k => FiniteMap Tree k v where
  empty = Leaf

  insert k v Leaf = Node k v Leaf Leaf
  insert k v (Node k' v' tˡ tʳ) =
    case compare k k' of
      LT -> Node k' v' (insert k v tˡ) tʳ
      EQ -> Node k  v  tˡ              tʳ
      GT -> Node k' v' tˡ (insert k v tʳ)

  lookup k Leaf = Nothing
  lookup k (Node k' v' tˡ tʳ) =
    case compare k k' of
      LT -> lookup k tˡ
      EQ -> Just v'
      GT -> lookup k tʳ
