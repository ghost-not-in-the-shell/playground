module Prelude.Maybe where
open import Prelude.Equality
open import Prelude.Function
open import Prelude.Op

data Maybe (A : Set) : Set where
  nothing :     Maybe A
  just    : A → Maybe A

maybe : ∀ {A B} → (A → B) → (Maybe A → Maybe B)
maybe f nothing  = nothing
maybe f (just x) = just (f x)

maybe-id : ∀ {A} (m : Maybe A) → maybe id m ≡ m
maybe-id nothing  = refl
maybe-id (just x) = refl

maybe-∘ : ∀ {A B C} {f : A → B} {g : B → C} (m : Maybe A)
  → maybe (g ∘ f) m ≡ (maybe g ∘ maybe f) m
maybe-∘ nothing  = refl
maybe-∘ (just x) = refl
