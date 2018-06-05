module Jellyfish.Prelude.Subset where
open import Jellyfish.Prelude.List
open import Jellyfish.Prelude.Equality

data Side {𝔞} {A : Set 𝔞} : A → Set 𝔞 where
  outside : ∀ {x} → Side x
  inside  : ∀ {x} → Side x

Subset : ∀ {𝔞} {A : Set 𝔞} → List A → Set 𝔞
Subset = All Side

∅ : ∀ {𝔞} {A : Set 𝔞} {xs : List A} → Subset xs
∅ {xs = ε}      = ε
∅ {xs = xs ▻ x} = ∅ ▻ outside

infixr 6 _∪_
_∪_ : ∀ {𝔞} {A : Set 𝔞} {xs : List A} → Subset xs → Subset xs → Subset xs
ε               ∪ ε               = ε
(⌊xs⌋₁ ▻ outside) ∪ (⌊xs⌋₂ ▻ outside) = ⌊xs⌋₁ ∪ ⌊xs⌋₂ ▻ outside
(⌊xs⌋₁ ▻ outside) ∪ (⌊xs⌋₂ ▻  inside) = ⌊xs⌋₁ ∪ ⌊xs⌋₂ ▻  inside
(⌊xs⌋₁ ▻  inside) ∪ (⌊xs⌋₂ ▻       _) = ⌊xs⌋₁ ∪ ⌊xs⌋₂ ▻  inside

⁅_⁆ : ∀ {𝔞} {A : Set 𝔞} {xs : List A} {x} → xs ∋ x → Subset xs
⁅ ze   ⁆ =   ∅   ▻  inside
⁅ su i ⁆ = ⁅ i ⁆ ▻ outside

↑⁽_⁾_ : ∀ {𝔞} {A : Set 𝔞} {xs : List A} x → Subset xs → Subset (xs ▻ x)
↑⁽ x ⁾ ⌊xs⌋ = ⌊xs⌋ ▻ inside

↓⁽_⁾_ : ∀ {𝔞} {A : Set 𝔞} {xs : List A} x → Subset (xs ▻ x) → Subset xs
↓⁽ x ⁾ (⌊xs⌋ ▻ y) = ⌊xs⌋

↑_ : ∀ {𝔞} {A : Set 𝔞} {xs : List A} {x} → Subset xs → Subset (xs ▻ x)
↑ ⌊xs⌋ = ↑⁽ _ ⁾ ⌊xs⌋

↓_ : ∀ {𝔞} {A : Set 𝔞} {xs : List A} {x} → Subset (xs ▻ x) → Subset xs
↓ ⌊xs⌋ = ↓⁽ _ ⁾ ⌊xs⌋

⌈_⌉ : ∀ {𝔞} {A : Set 𝔞} {xs : List A} → Subset xs → List A
⌈_⌉ ε = ε
⌈_⌉ (⌊xs⌋ ▻ outside    ) = ⌈ ⌊xs⌋ ⌉
⌈_⌉ (⌊xs⌋ ▻  inside {x}) = ⌈ ⌊xs⌋ ⌉ ▻ x

trim : ∀ {𝔞 𝔭} {A : Set 𝔞} {P : A → Set 𝔭} {xs : List A} (⌊xs⌋ : Subset xs) → All P xs → All P ⌈ ⌊xs⌋ ⌉
trim ε ε = ε
trim (⌊xs⌋ ▻ outside) (pxs ▻ px) = trim ⌊xs⌋ pxs
trim (⌊xs⌋ ▻  inside) (pxs ▻ px) = trim ⌊xs⌋ pxs ▻ px

∪-identityˡ : ∀ {𝔞} {A : Set 𝔞} {xs : List A} (⌊xs⌋ : Subset xs) → ∅ ∪ ⌊xs⌋ ≡ ⌊xs⌋
∪-identityˡ ε = refl
∪-identityˡ (⌊xs⌋ ▻ outside) = _▻ outside ⟨$⟩ ∪-identityˡ ⌊xs⌋
∪-identityˡ (⌊xs⌋ ▻  inside) = _▻  inside ⟨$⟩ ∪-identityˡ ⌊xs⌋

∪-identityʳ : ∀ {𝔞} {A : Set 𝔞} {xs : List A} (⌊xs⌋ : Subset xs) → ⌊xs⌋ ∪ ∅ ≡ ⌊xs⌋
∪-identityʳ ε = refl
∪-identityʳ (⌊xs⌋ ▻ outside) = _▻ outside ⟨$⟩ ∪-identityʳ ⌊xs⌋
∪-identityʳ (⌊xs⌋ ▻  inside) = _▻  inside ⟨$⟩ ∪-identityʳ ⌊xs⌋

↑↓≡∪⁅ze⁆ : ∀ {𝔞} {A : Set 𝔞} {xs : List A} {x} (⌊xs⌋ : Subset (xs ▻ x)) → ↑ ↓ ⌊xs⌋ ≡ ⌊xs⌋ ∪ ⁅ ze ⁆
↑↓≡∪⁅ze⁆ (⌊xs⌋ ▻ outside) rewrite ∪-identityʳ ⌊xs⌋ = refl
↑↓≡∪⁅ze⁆ (⌊xs⌋ ▻  inside) rewrite ∪-identityʳ ⌊xs⌋ = refl
