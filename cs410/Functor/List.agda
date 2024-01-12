module Functor.List where
open import Prelude
open import Category

list : ∀ {A B} → (A → B) → (List A → List B)
list f []       = []
list f (x ∷ xs) = f x ∷ list f xs

list-id : ∀ {A} (xs : List A) → list id xs ≡ xs
list-id []       = refl
list-id (x ∷ xs) = ⦇ refl ∷ list-id xs ⦈

list-∘ : ∀ {A B C} {f : A → B} {g : B → C} (xs : List A) → list (g ∘ f) xs ≡ (list g ∘ list f) xs
list-∘ []       = refl
list-∘ (x ∷ xs) = ⦇ refl ∷ list-∘ xs ⦈

𝓛𝓲𝓼𝓽 : 𝓢𝓮𝓽 ⟶ 𝓢𝓮𝓽
𝓛𝓲𝓼𝓽 = record
  { map₀ = List
  ; map₁ = list
  ; resp-id = λ⁼ list-id
  ; resp-∘  = λ⁼ list-∘
  }
