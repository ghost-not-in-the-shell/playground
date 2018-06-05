module Jellyfish.Core.Syntax.Raw where
open import Jellyfish.Prelude

data Tm : Set where
  lit : Nat → Tm
  add : Tm → Tm → Tm
  sub : Tm → Tm → Tm
  mul : Tm → Tm → Tm
  ifz : Tm → Tm → Tm → Tm
  var : String → Tm
  lam : String → Tm → Tm
  app : Tm → Tm → Tm
  lεt : String → Tm → Tm → Tm
  the : Ty → Tm → Tm
