module Diagram.Terminal 𝓒 where
open import Prelude
open import Category.Base

is-terminal : Ob 𝓒 → Type
is-terminal 𝟙 = ∀ X → is-contr (𝓒 ⦅ X , 𝟙 ⦆)

record Terminal : Type where
  field
    apex : Ob 𝓒
    terminal : is-terminal apex

  !′ : ∀ {X} → 𝓒 ⦅ X , apex ⦆
  !′ {X} = terminal X .centre

  unique : ∀ {X} {⁇ : 𝓒 ⦅ X , apex ⦆} → ⁇ ≡ !′
  unique {X} {⁇} = sym (terminal X .connect ⁇)

instance
  terminalOp : ⦃ _ : Terminal ⦄ → TerminalOp (Hom 𝓒)
  terminalOp ⦃ term ⦄ = record
    { 𝟙 = apex term
    ; ! = !′   term
    } where open Terminal

module 𝟙 ⦃ term : Terminal ⦄ where
  module _ where
    open Terminal term public hiding (apex; !′)
