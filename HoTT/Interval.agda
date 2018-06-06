module Interval where
open import Identity

data I : Set where
  𝟘 : I
  𝟙 : I
postulate
  seg : 𝟘 ≡ 𝟙

rec⟦I⟧ : ∀ {𝔟} (B : Set 𝔟) (b₀ b₁ : B) (s : b₀ ≡ b₁) → I → B
rec⟦I⟧ B b₀ b₁ s 𝟘 = b₀
rec⟦I⟧ B b₀ b₁ s 𝟙 = b₁
postulate
  βrec⟦I⟧ : ∀ {𝔟} (B : Set 𝔟) (b₀ b₁ : B) (s : b₀ ≡ b₁) → ap (rec⟦I⟧ B b₀ b₁ s) seg ≡ s

ind⟦I⟧ : ∀ {𝔭} (P : I → Set 𝔭) (b₀ : P 𝟘) (b₁ : P 𝟙) (s : b₀ ≡ b₁ [ P ↓ seg ]) → ∀ x → P x
ind⟦I⟧ P b₀ b₁ s 𝟘 = b₀
ind⟦I⟧ P b₀ b₁ s 𝟙 = b₁
postulate
  βind⟦I⟧ : ∀ {𝔭} (P : I → Set 𝔭) (b₀ : P 𝟘) (b₁ : P 𝟙) (s : b₀ ≡ b₁ [ P ↓ seg ]) → apd (ind⟦I⟧ P b₀ b₁ s) seg ≡ s

