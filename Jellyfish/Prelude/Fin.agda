module Jellyfish.Prelude.Fin where
open import Jellyfish.Prelude.Nat

data Fin : Nat → Set where
  zero : ∀ {n}         → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)
