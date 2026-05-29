module Prelude.Cubical.Iso where
open import Prelude.Prim
open import Prelude.Cubical.Base
open import Prelude.Cubical.Observational
open import Prelude.Idiom

is-inj : ∀ {A B} → Function A B → Type
is-inj f = ∀ {x y} → f x ≡ f y → x ≡ y

is-surj : ∀ {A B} → Function A B → Type
is-surj {A} {B} f = (b : B) → Σ[ a ∈ A ] f a ≡ b

module _ {A B} (f : Function A B) where
  inj∧surj→iso : is-inj f → is-surj f → is-iso Function f
  inj∧surj→iso f-inj f-surj = record
    { bwd = f⁻¹
    ; ∘-invˡ = ∘-invˡ′
    ; ∘-invʳ = ∘-invʳ′
    } where f⁻¹ : B → A
            f⁻¹ b = f-surj b .fst

            ∘-invˡ′ : f⁻¹ ∘ f ≡ id
            ∘-invˡ′ = ext λ a → f-inj (f-surj (f a) .snd)

            ∘-invʳ′ : f ∘ f⁻¹ ≡ id
            ∘-invʳ′ = ext λ b → f-surj b .snd

  iso→inj : ⦃ is-iso Function f ⦄ → is-inj f
  iso→inj {x} {y} hyp = begin
              x  ≡⟨ invˡ f ⟨
    (f ⁻¹ $ f x) ≡⟨ cong (f ⁻¹) hyp ⟩
    (f ⁻¹ $ f y) ≡⟨ invˡ f ⟩
              y  ∎

  iso→surj : ⦃ is-iso Function f ⦄ → is-surj f
  iso→surj = λ b → ((f ⁻¹ $ b) , invʳ f)
