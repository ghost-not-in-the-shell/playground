module Functor.Maybe where
open import Prelude
open import Category

maybe : ∀ {A B} → (A → B) → (Maybe A → Maybe B)
maybe f nothing  = nothing
maybe f (just x) = just (f x)

maybe-id : ∀ {A} (m : Maybe A) → maybe id m ≡ m
maybe-id nothing  = refl
maybe-id (just x) = cong just refl

maybe-∘ : ∀ {A B C} {f : A → B} {g : B → C} (m : Maybe A) → maybe (g ∘ f) m ≡ (maybe g ∘ maybe f) m
maybe-∘ nothing  = refl
maybe-∘ (just x) = cong just refl

𝓜𝓪𝔂𝓫𝓮 : 𝓢𝓮𝓽 ⟶ 𝓢𝓮𝓽
𝓜𝓪𝔂𝓫𝓮 = record
  { map₀ = Maybe
  ; map₁ = maybe
  ; resp-id = λ⁼ maybe-id
  ; resp-∘  = λ⁼ maybe-∘
  }
