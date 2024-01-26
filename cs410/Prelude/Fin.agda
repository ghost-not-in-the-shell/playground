module Prelude.Fin where
open import Prelude.Nat

data Fin : ℕ → Set where
  zero : ∀ {n}         → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)
