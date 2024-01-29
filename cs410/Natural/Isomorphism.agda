open import Category.Base
open import Functor.Base
module Natural.Isomorphism {𝓒 𝓓} {𝓕 𝓖 : 𝓒 ⟶ 𝓓} where
open import Prelude
open import Category.Functor
open import Category.Isomorphism
open import Natural.Base

to-component≅ : ∀ {α : 𝓕 ⟹ 𝓖}
  → Isomorphism (𝓕𝓾𝓷 𝓒 𝓓) α
  → (∀ {A} → Isomorphism 𝓓 (α ₍ A ₎))
to-component≅ α {A} = record
  { inverse = ∣ α ⁻¹ ∣ ₍ A ₎
  ; isoˡ = cong _₍ A ₎ $ isoˡ α
  ; isoʳ = cong _₍ A ₎ $ isoʳ α
  }

from-component≅ : ∀ {α : 𝓕 ⟹ 𝓖}
  → (∀ {A} → Isomorphism 𝓓 (α ₍ A ₎))
  → Isomorphism (𝓕𝓾𝓷 𝓒 𝓓) α
from-component≅ {_ , natural} α = record
  { inverse = record
    { component = ∣ α ⁻¹ ∣
    ; natural = λ { {f = f} → cancelʳ α (begin
      (∣ α ⁻¹ ∣ ∘ 𝓖 ₁(f)) ∘ ∣ α ∣  ≡⟨ ∘-assoc 𝓓 ⟩
      ∣ α ⁻¹ ∣ ∘ (𝓖 ₁(f) ∘ ∣ α ∣)  ≡⟨ sym ⦇ refl ∘ natural ⦈ ⟩
      ∣ α ⁻¹ ∣ ∘ (∣ α ∣ ∘ 𝓕 ₁(f))  ≡⟨ sym $ ∘-assoc 𝓓 ⟩
      (∣ α ⁻¹ ∣ ∘ ∣ α ∣) ∘ 𝓕 ₁(f)  ≡⟨ ⦇ isoˡ α ∘ refl ⦈ ⟩
      id ∘ 𝓕 ₁(f)                  ≡⟨ trans (∘-identityˡ 𝓓) (sym $ ∘-identityʳ 𝓓) ⟩
      𝓕 ₁(f) ∘ id                  ≡⟨ sym ⦇ refl ∘ isoˡ α ⦈ ⟩
      𝓕 ₁(f) ∘ (∣ α ⁻¹ ∣ ∘ ∣ α ∣)  ≡⟨ sym $ ∘-assoc 𝓓 ⟩
      (𝓕 ₁(f) ∘ ∣ α ⁻¹ ∣) ∘ ∣ α ∣  ∎) }
    }
  ; isoˡ = natural⁼ $ ƛ⁼ $ isoˡ α
  ; isoʳ = natural⁼ $ ƛ⁼ $ isoʳ α
  }
