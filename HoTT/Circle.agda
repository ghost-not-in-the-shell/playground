module Circle where
open import Identity

data S¹ : Set where
  base : S¹
postulate
  loop : base ≡ base

rec⟦S¹⟧ : ∀ {𝔟} (B : Set 𝔟) (b : B) (l : b ≡ b) → S¹ → B
rec⟦S¹⟧ B b l base = b
postulate
  βrec⟦S¹⟧ : ∀ {𝔟} (B : Set 𝔟) (b : B) (l : b ≡ b) → ap (rec⟦S¹⟧ B b l) loop ≡ l

ind⟦S¹⟧ : ∀ {𝔭} (P : S¹ → Set 𝔭) (b : P base) (l : b ≡ b [ P ↓ loop ]) → ∀ x → P x
ind⟦S¹⟧ P b l base = b
postulate
  βind⟦S¹⟧ : ∀ {𝔭} (P : S¹ → Set 𝔭) (b : P base) (l : b ≡ b [ P ↓ loop ]) → apd (ind⟦S¹⟧ P b l) loop ≡ l
