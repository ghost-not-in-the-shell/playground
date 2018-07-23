{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UnicodeSyntax #-}
module LeftistHeap where
import PriorityQueue

data Tree k v
  = Leaf
  | Node Int k v (Tree k v) (Tree k v)
  deriving (Show)

rank :: Tree k v -> Int
rank Leaf = 0
rank (Node r _ _ _ _) = r

makeNode :: k -> v -> Tree k v -> Tree k v -> Tree k v
makeNode k v tˡ tʳ = if rank tˡ >= rank tʳ
                     then Node (rank tʳ + 1) k v tˡ tʳ
                     else Node (rank tˡ + 1) k v tʳ tˡ

merge :: Ord k => Tree k v -> Tree k v -> Tree k v
merge Leaf t = t
merge t Leaf = t
merge t₁@(Node _ k₁ v₁ tˡ₁ tʳ₁) t₂@(Node _ k₂ v₂ tˡ₂ tʳ₂) =
  if k₁ <= k₂
  then makeNode k₁ v₁ tˡ₁ (merge tʳ₁ t₂)
  else makeNode k₂ v₂ tˡ₂ (merge t₁ tʳ₂)

instance Ord k => PriorityQueue Tree k v where
  empty = Leaf

  insert k v t = merge (Node 1 k v Leaf Leaf) t

  getMin Leaf = Nothing
  getMin (Node _ k v tˡ tʳ) = Just v

  deleteMin Leaf = Nothing
  deleteMin (Node _ k v tˡ tʳ) = Just $ merge tˡ tʳ
