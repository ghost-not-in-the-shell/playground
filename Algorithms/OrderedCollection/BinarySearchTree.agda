open import Algorithms.StrictTotalOrder
module Algorithms.OrderedCollection.BinarySearchTree {𝑘 ℓ 𝑣} (⟨Key,<⟩ : StrictTotalOrder 𝑘 ℓ) (Value : Set 𝑣) where
open StrictTotalOrder ⟨Key,<⟩ renaming (Carrier to Key)
open import Algorithms.OrderedCollection.Bounded ⟨Key,<⟩ renaming (A⁺ to Key⁺)
open import Algorithms.Equality
open import Algorithms.Miscellaneous

data Tree⊂₍_,_₎ (l u : Key⁺) : Set (𝑘 ⊔ ℓ ⊔ 𝑣) where
  leaf : l <⁺ u → Tree⊂₍ l , u ₎
  node : ∀ (k : Key) (v : Value)
    → Tree⊂₍ l   , k ⁺ ₎
    → Tree⊂₍ k ⁺ , u   ₎
    → Tree⊂₍ l   , u   ₎

empty : Tree⊂₍ -∞ , +∞ ₎
empty = leaf ∞

insert< : ∀ {l u} (k : Key) (v : Value)
  → l <⁺ k ⁺ <⁺ u
  → Tree⊂₍ l , u ₎
  → Tree⊂₍ l , u ₎
insert< k v (l<k , k<u) (leaf _) = node k v (leaf l<k) (leaf k<u)
insert< k v (l<k , k<u) (node k′ v′ tˡ tʳ) with compare k k′
... | tri< k<k′ _ _ = node k′ v′ (insert< k v (l<k , k<k′ ⁺) tˡ) tʳ
... | tri≡ _ refl _ = node k  v  tˡ                              tʳ
... | tri> _ _ k′<k = node k′ v′ tˡ (insert< k v (k′<k ⁺ , k<u) tʳ)

insert : ∀ (k : Key) (v : Value) → Tree⊂₍ -∞ , +∞ ₎ → Tree⊂₍ -∞ , +∞ ₎
insert k v t = insert< k v (-∞ , +∞) t

lookup : ∀ {l u} k → Tree⊂₍ l , u ₎ → Maybe Value
lookup k (leaf _) = nothing
lookup k (node k′ v′ tˡ tʳ) with compare k k′
... | lt = lookup k tˡ
... | eq = just v′
... | gt = lookup k tʳ
