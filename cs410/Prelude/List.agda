module Prelude.List where
open import Prelude.Equality
open import Prelude.Function
open import Prelude.Op

infixr 5 _∷_
data List (A : Set) : Set where
  []  :              List A
  _∷_ : A → List A → List A

list : ∀ {A B} → (A → B) → (List A → List B)
list f [] = []
list f (x ∷ xs) = f x ∷ list f xs

list-id : ∀ {A} (xs : List A) → list id xs ≡ xs
list-id [] = refl
list-id (x ∷ xs) = ⦇ refl ∷ list-id xs ⦈

list-∘ : ∀ {A B C} {f : A → B} {g : B → C} (xs : List A)
  → list (g ∘ f) xs ≡ (list g ∘ list f) xs
list-∘ [] = refl
list-∘ (x ∷ xs) = ⦇ refl ∷ list-∘ xs ⦈
