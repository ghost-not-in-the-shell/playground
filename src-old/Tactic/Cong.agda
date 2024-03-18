module Tactic.Cong where
open import Prelude.Reflection

record Equality : Set where
  constructor equals
  field
    {type} : Term
    lhs : Term
    rhs : Term

destruct-equality : Term → TC Equality
destruct-equality eq@(def (quote _≡_)
