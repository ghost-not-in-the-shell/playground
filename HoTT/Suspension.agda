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
  βrec⟦∑_⟧ : ∀ {𝔞 𝔟} (A : Set 𝔞) (B : Set 𝔟) (n s : B) (m : A → n ≡ s) → ∀ a → ap (rec⟦∑ A ⟧ B n s m) (merid a) ≡ m a
