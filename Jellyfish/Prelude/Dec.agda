module Jellyfish.Prelude.Dec where
open import Jellyfish.Prelude.Sum
open import Jellyfish.Prelude.Empty

Dec : ∀ {𝔭} (P : Set 𝔭) → Set 𝔭
Dec P = P ∐ ¬ P

pattern yes p = inj₁ p
pattern no ¬p = inj₂ ¬p
