module Adjoint.UnitCounit where
open import Prelude
open import Category.Base
open import Functor.Base
open import Natural.Base

record Adjoint {𝓒 𝓓} (𝐿 : 𝓒 ⟶ 𝓓) (𝑅 : 𝓓 ⟶ 𝓒) : Type where
  field
    unit   : id ⟹ 𝑅 ∘ 𝐿
    counit : 𝐿 ∘ 𝑅 ⟹ id

  private
    η = unit
    ε = counit

  field
    zig : ∀ {A} → ε ₍ 𝐿 ₀(A) ₎ ∘ 𝐿 ₁(η ₍ A ₎) ≡ id
    zag : ∀ {S} → 𝑅 ₁(ε ₍ S ₎) ∘ η ₍ 𝑅 ₀(S) ₎ ≡ id

infix 4 _⊣_
_⊣_ = Adjoint

private module Duality where
  instance
    opposite-adjunction : ∀ {𝓒 𝓓} {𝐿 : 𝓒 ⟶ 𝓓} {𝑅 : 𝓓 ⟶ 𝓒}
      → Opposite (𝐿 ⊣ 𝑅) (𝑅 ᵒᵖ ⊣ 𝐿 ᵒᵖ)
    opposite-adjunction = record
      { opposite = λ adj → let open Adjoint adj in record
        { unit   = counit ᵒᵖ
        ; counit = unit ᵒᵖ
        ; zig = zag
        ; zag = zig
        }
      }

  _ : ∀ {𝓒 𝓓} {𝐿 : 𝓒 ⟶ 𝓓} {𝑅 : 𝓓 ⟶ 𝓒} {adj : 𝐿 ⊣ 𝑅} → (adj ᵒᵖ)ᵒᵖ ≡ adj
  _ = refl

open Duality public
