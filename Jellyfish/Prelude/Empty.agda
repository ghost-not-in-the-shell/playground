module Jellyfish.Prelude.Empty where
open import Jellyfish.Prelude.Sum

data ⊥ : Set where

⊥-elim : ∀ {𝔠} {C : Set 𝔠} → ⊥ → C
⊥-elim ()

¬_ : ∀ {𝔭} (P : Set 𝔭) → Set 𝔭
¬ P = P → ⊥

_↯_ : ∀ {𝔭 𝔮} {P : Set 𝔭} {Q : Set 𝔮} → P → ¬ P → Q
p ↯ ¬p = ⊥-elim (¬p p)
