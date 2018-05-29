{- Not the best solution...
   Still need to learn well-founded induction in order to
   make it pass the termination check...
   https://stackoverflow.com/questions/22265402/merge-sort-in-agda
-}
module Algorithms.MergeSort where
open import Data.Bool
open import Data.List
open import Data.Nat
open import Data.Product
open import Relation.Nullary.Decidable

merge : List ℕ → List ℕ → List ℕ
merge [] xs₂ = xs₂
merge xs₁ [] = xs₁
merge (x₁ ∷ xs₁) (x₂ ∷ xs₂) = if ⌊ x₁ ≤? x₂ ⌋
                          then x₁ ∷ merge xs₁ (x₂ ∷ xs₂)
                          else x₂ ∷ merge (x₁ ∷ xs₁) xs₂

{-# TERMINATING #-}
sort : List ℕ → List ℕ
sort []       = []
sort (x ∷ []) = [ x ]
sort xs = let (xs₁ , xs₂) = splitAt ⌊ length xs /2⌋ xs
          in merge (sort xs₁) (sort xs₂)
