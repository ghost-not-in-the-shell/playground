module Jellyfish.Prelude.Function where

_∘_ : ∀ {𝔞 𝔟 𝔠} {A : Set 𝔞} {B : A → Set 𝔟} {C : ∀ {x} → B x → Set 𝔠}
  → (g : ∀ {x} (y : B x) → C y)
  → (f : ∀ x → B x)
  → ∀ x → C (f x)
g ∘ f = λ x → g (f x)

case_of_ : ∀ {𝔞 𝔟} {A : Set 𝔞} {B : A → Set 𝔟} → ∀ x → (∀ x → B x) → B x
case x of f = f x
