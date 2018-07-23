{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, NoImplicitPrelude, UnicodeSyntax #-}
module RedBlackTree where
import FiniteMap
import Prelude hiding (lookup)

data Color = R | B deriving (Show)

data Tree k v
  = Leaf
  | Node Color k v (Tree k v) (Tree k v)
  deriving (Show)

instance Ord k => FiniteMap Tree k v where
  empty = Leaf

  insert k v t = blackenRoot (ins k v t)
    where balance :: Color -> k -> v -> Tree k v -> Tree k v -> Tree k v
          balance B kʳ vʳ (Node R k v (Node R kˡ vˡ t₁ t₂) t₃) t₄
            = Node R k v (Node B kˡ vˡ t₁ t₂) (Node B kʳ vʳ t₃ t₄)
          balance B kʳ vʳ (Node R kˡ vˡ t₁ (Node R k v t₂ t₃)) t₄
            = Node R k v (Node B kˡ vˡ t₁ t₂) (Node B kʳ vʳ t₃ t₄)
          balance B kˡ vˡ t₁ (Node R kʳ vʳ (Node R k v t₂ t₃) t₄)
            = Node R k v (Node B kˡ vˡ t₁ t₂) (Node B kʳ vʳ t₃ t₄)
          balance B kˡ vˡ t₁ (Node R k v t₂ (Node R kˡ vˡ t₃ t₄))
            = Node R k v (Node B kˡ vˡ t₁ t₂) (Node B kʳ vʳ t₃ t₄)
          balance = Node

          ins :: Ord k => k -> v -> Tree k v -> Tree k v
          ins k v Leaf = Node R k v Leaf Leaf
          ins k v (Node c k' v' tˡ tʳ) =
            case compare k k' of
              LT -> balance c k' v' (ins k v tˡ) tʳ
              EQ -> Node    c k  v  tˡ           tʳ
              GT -> balance c k' v' tˡ (ins k v tʳ)

          blackenRoot :: Tree k v -> Tree k v
          blackenRoot Leaf = Leaf
          blackenRoot (Node _ k v tˡ tʳ) = Node B k v tˡ tʳ

  lookup k Leaf = Nothing
  lookup k (Node _ k' v' tˡ tʳ) =
    case compare k k' of
      LT -> lookup k tˡ
      EQ -> Just v'
      GT -> lookup k tʳ
