module Algorithms.InsertionSort where
open import Data.Bool
open import Data.List
open import Data.Nat
open import Relation.Nullary.Decidable

insert : ℕ → List ℕ → List ℕ
insert key []       = [ key ]
insert key (x ∷ xs) = if ⌊ key ≤? x ⌋
                      then key ∷ x ∷ xs
                      else x ∷ insert key xs

sort : List ℕ → List ℕ
sort []       = []
sort (x ∷ xs) = insert x (sort xs)
