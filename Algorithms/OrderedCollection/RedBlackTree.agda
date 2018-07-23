open import Algorithms.StrictTotalOrder
module Algorithms.OrderedCollection.RedBlackTree {𝑘 ℓ 𝑣} (⟨Key,<⟩ : StrictTotalOrder 𝑘 ℓ) (Value : Set 𝑣) where
open StrictTotalOrder ⟨Key,<⟩ renaming (Carrier to Key)
open import Algorithms.OrderedCollection.Bounded ⟨Key,<⟩ renaming (A⁺ to Key⁺)
open import Algorithms.Equality
open import Algorithms.Miscellaneous

data Color (h : ℕ) : ℕ → Set where
  ○ : Color h      h
  ● : Color h (suc h)

mutual
  data Tree⊂₍_,_₎ (l u : Key⁺) : ℕ → Set (𝑘 ⊔ ℓ ⊔ 𝑣) where
    leaf  : l <⁺ u → Tree⊂₍ l , u ₎ zero
    node○ : ∀ {h} (k : Key) (v : Value)
      → Tree⊂₍ l   , k ⁺ ₎● h
      → Tree⊂₍ k ⁺ , u   ₎● h
      → Tree⊂₍ l   , u   ₎  h
    node● : ∀ {h} (k : Key) (v : Value)
      → Tree⊂₍ l   , k ⁺ ₎      h
      → Tree⊂₍ k ⁺ , u   ₎      h
      → Tree⊂₍ l   , u   ₎ (suc h)

  data Tree⊂₍_,_₎● (l u : Key⁺) : ℕ → Set (𝑘 ⊔ ℓ ⊔ 𝑣) where
    leaf  : l <⁺ u → Tree⊂₍ l , u ₎● zero
    node● : ∀ {h} (k : Key) (v : Value)
      → Tree⊂₍ l   , k ⁺ ₎       h
      → Tree⊂₍ k ⁺ , u   ₎       h
      → Tree⊂₍ l   , u   ₎● (suc h)

data Tree⊂₍_,_₎○ (l u : Key⁺) : ℕ → Set (𝑘 ⊔ ℓ ⊔ 𝑣) where
  node○ : ∀ {h} (k : Key) (v : Value)
    → Tree⊂₍ l   , k ⁺ ₎● h
    → Tree⊂₍ k ⁺ , u   ₎● h
    → Tree⊂₍ l   , u   ₎○ h

from● : ∀ {l u h} → Tree⊂₍ l , u ₎● h → Tree⊂₍ l , u ₎ h
from● (leaf l<u)        = leaf l<u
from● (node● k v tˡ tʳ) = node● k v tˡ tʳ

inspect : ∀ {l u h}
  → Tree⊂₍ l , u ₎ h
  → Tree⊂₍ l , u ₎○ h ⊎ Tree⊂₍ l , u ₎● h
inspect (leaf l<u)        = inj₂ (leaf l<u)
inspect (node○ k v tˡ tʳ) = inj₁ (node○ k v tˡ tʳ)
inspect (node● k v tˡ tʳ) = inj₂ (node● k v tˡ tʳ)

data Tree⊂₍_,_₎🚧 (l u : Key⁺) : ℕ → Set (𝑘 ⊔ ℓ ⊔ 𝑣) where
  leaf : l <⁺ u → Tree⊂₍ l , u ₎🚧 zero
  node : ∀ {h₁ h₂} (c : Color h₁ h₂) (k : Key) (v : Value)
    → Tree⊂₍ l   , k ⁺ ₎   h₁
    → Tree⊂₍ k ⁺ , u   ₎   h₁
    → Tree⊂₍ l   , u   ₎🚧 h₂

🚧 : ∀ {l u h}
  → Tree⊂₍ l , u ₎   h
  → Tree⊂₍ l , u ₎🚧 h
🚧 (leaf l<u)        = leaf l<u
🚧 (node○ k v tˡ tʳ) = node ○ k v (from● tˡ) (from● tʳ)
🚧 (node● k v tˡ tʳ) = node ● k v        tˡ         tʳ

balanceˡ : ∀ {l u h} (k : Key) (v : Value)
  → Tree⊂₍ l   , k ⁺ ₎🚧    h
  → Tree⊂₍ k ⁺ , u   ₎      h
  → Tree⊂₍ l   , u   ₎ (suc h)
balanceˡ kʳ vʳ (node ○ k v (node○ kˡ vˡ t₁ t₂) t₃) t₄
  = node○ k v (node● kˡ vˡ (from● t₁) (from● t₂)) (node● kʳ vʳ t₃ t₄)
balanceˡ kʳ vʳ (node ○ kˡ vˡ t₁ (node○ k v t₂ t₃)) t₄
  = node○ k v (node● kˡ vˡ t₁ (from● t₂)) (node● kʳ vʳ (from● t₃) t₄)
balanceˡ k v (leaf l<k) t
  = node● k v (leaf l<k) t
balanceˡ k v (node ○ kˡ vˡ (leaf l<kˡ) (leaf kˡ<k)) t
  = node● k v (node○ kˡ vˡ (leaf l<kˡ) (leaf kˡ<k)) t
balanceˡ k v (node ○ kˡ vˡ (node● kˡˡ vˡˡ t₁ t₂) (node● kˡʳ vˡʳ t₃ t₄)) t₅
  = node● k v (node○ kˡ vˡ (node● kˡˡ vˡˡ t₁ t₂) (node● kˡʳ vˡʳ t₃ t₄)) t₅
balanceˡ k v (node ● kˡ vˡ t₁ t₂) t₃
  = node● k v (node● kˡ vˡ t₁ t₂) t₃

balanceʳ : ∀ {l u h} (k : Key) (v : Value)
  → Tree⊂₍ l   , k ⁺ ₎      h
  → Tree⊂₍ k ⁺ , u   ₎🚧    h
  → Tree⊂₍ l   , u   ₎ (suc h)
balanceʳ kˡ vˡ t₁ (node ○ kʳ vʳ (node○ k v t₂ t₃) t₄)
  = node○ k v (node● kˡ vˡ t₁ (from● t₂)) (node● kʳ vʳ (from● t₃) t₄)
balanceʳ kˡ vˡ t₁ (node ○ k v t₂ (node○ kʳ vʳ t₃ t₄))
  = node○ k v (node● kˡ vˡ t₁ t₂) (node● kʳ vʳ (from● t₃) (from● t₄))
balanceʳ k v t (leaf k<u)
  = node● k v t (leaf k<u)
balanceʳ k v t (node ○ kʳ vʳ (leaf k<kʳ) (leaf kʳ<u))
  = node● k v t (node○ kʳ vʳ (leaf k<kʳ) (leaf kʳ<u))
balanceʳ k v t₁ (node ○ kʳ vʳ (node● kʳˡ vʳˡ t₂ t₃) (node● kʳʳ vʳʳ t₄ t₅))
  = node● k v t₁ (node○ kʳ vʳ (node● kʳˡ vʳˡ t₂ t₃) (node● kʳʳ vʳʳ t₄ t₅))
balanceʳ k v t₁ (node ● kʳ vʳ t₂ t₃)
  = node● k v t₁ (node● kʳ vʳ t₂ t₃)

mutual
  ins○ : ∀ {l u h} (k : Key) (v : Value)
    → l <⁺ k ⁺ <⁺ u
    → Tree⊂₍ l , u ₎○  h
    → Tree⊂₍ l , u ₎🚧 h
  ins○ k v (l<k , k<u) (node○ k′ v′ tˡ tʳ) with compare k k′
  ... | tri< k<k′ _ _ = node ○ k′ v′ (ins● k v (l<k , k<k′ ⁺) tˡ) (from● tʳ)
  ... | tri≡ _ refl _ = node ○ k′ v  (from● tˡ)                   (from● tʳ)
  ... | tri> _ _ k′<k = node ○ k′ v′ (from● tˡ) (ins● k v (k′<k ⁺ , k<u) tʳ)

  ins● : ∀ {l u h} (k : Key) (v : Value)
    → l <⁺ k ⁺ <⁺ u
    → Tree⊂₍ l , u ₎● h
    → Tree⊂₍ l , u ₎  h
  ins● k v (l<k , k<u) (leaf l<u) = node○ k v (leaf l<k) (leaf k<u)
  ins● k v (l<k , k<u) (node● k′ v′ tˡ tʳ) with compare k k′
  ... | tri< k<k′ _ _ = balanceˡ k′ v′ (ins k v (l<k , k<k′ ⁺) tˡ) tʳ
  ... | tri≡ _ refl _ = node●    k  v  tˡ                          tʳ
  ... | tri> _ _ k′<k = balanceʳ k′ v′ tˡ (ins k v (k′<k ⁺ , k<u) tʳ)

  ins : ∀ {l u h} (k : Key) (v : Value)
    → l <⁺ k ⁺ <⁺ u
    → Tree⊂₍ l , u ₎   h
    → Tree⊂₍ l , u ₎🚧 h
  ins k v (l<k , k<u) t with inspect t
  ... | inj₁ t○ =     ins○ k v (l<k , k<u) t○
  ... | inj₂ t● = 🚧 (ins● k v (l<k , k<u) t●)

blackenRoot : ∀ {l u h₁}
  →          Tree⊂₍ l , u ₎🚧 h₁
  → ∃ λ h₂ → Tree⊂₍ l , u ₎   h₂
blackenRoot (leaf l<u) = _ , leaf l<u
blackenRoot (node _ k v tˡ tʳ) = _ , node● k v tˡ tʳ

insert : ∀ {h₁} (k : Key) (v : Value)
  →          Tree⊂₍ -∞ , +∞ ₎ h₁
  → ∃ λ h₂ → Tree⊂₍ -∞ , +∞ ₎ h₂
insert k v t = blackenRoot (ins k v (-∞ , +∞) t)

empty : Tree⊂₍ -∞ , +∞ ₎ zero
empty = leaf ∞
