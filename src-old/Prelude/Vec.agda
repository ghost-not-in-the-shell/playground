module Prelude.Vec where
open import Prelude.Equality
open import Prelude.Function
open import Prelude.Fin
open import Prelude.Nat
open import Prelude.Op

infixr 5 _∷_
data Vec (A : Set) : ℕ → Set where
  []  :                       Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

vec : ∀ {n A B} → (A → B) → Vec A n → Vec B n
vec f [] = []
vec f (x ∷ xs) = f x ∷ vec f xs

infixr 5 _++_
_++_ : ∀ {A m n} → Vec A m → Vec A n → Vec A (m +ℕ n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

lookup : ∀ {A n} → Vec A n → Fin n → A
lookup (x ∷ xs) zero    = x
lookup (x ∷ xs) (suc i) = lookup xs i

vec-id : ∀ {n A} (xs : Vec A n) → vec id xs ≡ xs
vec-id [] = refl
vec-id (x ∷ xs) = ⦇ refl ∷ vec-id xs ⦈

vec-∘ : ∀ {n A B C} {f : A → B} {g : B → C} (xs : Vec A n) → vec (g ∘ f) xs ≡ (vec g ∘ vec f) xs
vec-∘ [] = refl
vec-∘ (x ∷ xs) = ⦇ refl ∷ vec-∘ xs ⦈
