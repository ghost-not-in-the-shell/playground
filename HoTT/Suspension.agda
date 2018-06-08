module Suspension where
open import Identity

data ∑_ {𝔞} (A : Set 𝔞) : Set 𝔞 where
  N : ∑ A
  S : ∑ A
postulate
  merid : ∀ {𝔞} {A : Set 𝔞} → A → N ≡₍ ∑ A ₎ S

rec⟦∑_⟧ : ∀ {𝔞 𝔟} (A : Set 𝔞) (B : Set 𝔟) (n s : B) (m : A → n ≡ s) → ∑ A → B
rec⟦∑ A ⟧ B n s m N = n
rec⟦∑ A ⟧ B n s m S = s
postulate
  βrec⟦∑_⟧ : ∀ {𝔞 𝔟} (A : Set 𝔞) (B : Set 𝔟) (n s : B) (m : A → n ≡ s)
    → ∀ a → ap (rec⟦∑ A ⟧ B n s m) (merid a) ≡ m a

ind⟦∑_⟧ : ∀ {𝔞 𝔭} (A : Set 𝔞) (P : ∑ A → Set 𝔭) (n : P N) (s : P S) (m : ∀ a → n ≡ s [ P ↓ merid a ]) → ∀ x → P x
ind⟦∑ A ⟧ P n s m N = n
ind⟦∑ A ⟧ P n s m S = s
postulate
  βind⟦∑_⟧ : ∀ {𝔞 𝔭} (A : Set 𝔞) (P : ∑ A → Set 𝔭) (n : P N) (s : P S) (m : ∀ a → n ≡ s [ P ↓ merid a ])
    → ∀ a → apd (ind⟦∑ A ⟧ P n s m) (merid a) ≡ m a
