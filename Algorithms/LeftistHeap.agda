open import Algorithms.TotalOrder
module Algorithms.LeftistHeap {𝑘 ℓ 𝑣} (⟨Key,<⟩ : TotalOrder 𝑘 ℓ) (Value : Set 𝑣) where
open TotalOrder ⟨Key,<⟩ renaming (Carrier to Key)
open import Algorithms.Bounded ⟨Key,<⟩ renaming
  (  A⁺     to  Key⁺
  ; ⟨A⁺,<⁺⟩ to ⟨Key⁺,<⁺⟩
  )
open import Algorithms.Equality
open import Algorithms.Miscellaneous

{-
data Heap : Key⁺ → ℕ → Set (𝑘 ⊔ ℓ ⊔ 𝑣) where
  leaf : Heap +∞ zero
  node : ∀ {kˡ kʳ hˡ hʳ} (k : Key) (v : Value)
    → hˡ ≥ hʳ
    → Heap  kˡ        hˡ → k ⁺ <⁺ kˡ
    → Heap  kʳ        hʳ → k ⁺ <⁺ kʳ
    → Heap (k ⁺) (suc hʳ)
-}

{-
merge : ∀ {k k′ h h′}
  → Heap k  h
  → Heap k′ h′
  → ∃ (Heap (min⁺ k k′))
merge {k′ = k′} leaf t′ with compare⁺ +∞ k′
... | tri< () _    _
... | tri≡ _  refl _ = _ , t′
... | tri> _  _    _ = _ , t′
merge {k = k} t leaf with compare⁺ k +∞
... | tri< _  _    _ = _ , t
... | tri≡ _  refl _ = _ , t
... | tri> _  _    ()
merge t@(node k v _ tˡ k<kˡ tʳ k<kʳ) t′@(node k′ v′ _ tˡ′ _ tʳ′ _) with compare k k′
... | tri< k<k′ _ _ = _ , node k v {!!} tˡ k<kˡ (snd (merge tʳ t′)) {!!}
... | tri≡ _ refl _ = {!!}
... | tri> _ _ k′<k = {!!}
-}
