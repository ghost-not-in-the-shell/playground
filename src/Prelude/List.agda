module Prelude.List where
open import Prelude.Idiom
open import Prelude.Nat

infixr 5 _∷_
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

{-# BUILTIN LIST List #-}

private
  variable
    A B C : Set

  map' : (A → B) → List A → List B
  map' f [] = []
  map' f (x ∷ xs) = f x ∷ map' f xs

  traverse' : ∀ {F : Effect} ⦃ _ : Applicative F ⦄ → (A → F B) → List A → F (List B)
  traverse' f [] = ⦇ [] ⦈
  traverse' f (x ∷ xs) = ⦇ f x ∷ traverse' f xs ⦈

instance
  List-map : Map List
  List-map = record { map = map' }

  List-traversable : Traversable List
  List-traversable = record { traverse = traverse' }

length : List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)
