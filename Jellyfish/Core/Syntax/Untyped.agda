module Jellyfish.Core.Syntax.Untyped where
open import Jellyfish.Prelude

data Tm (Γ : Nat) : Set where
  lit : Nat → Tm Γ
  add : Tm Γ → Tm Γ → Tm Γ
  sub : Tm Γ → Tm Γ → Tm Γ
  mul : Tm Γ → Tm Γ → Tm Γ
  ifz : Tm Γ → Tm Γ → Tm Γ → Tm Γ
  var : Fin Γ → Tm Γ
  lam : Tm (suc Γ) → Tm Γ
  app : Tm Γ → Tm Γ → Tm Γ
  lεt : Tm Γ → Tm (suc Γ) → Tm Γ
  the : Ty → Tm Γ → Tm Γ
