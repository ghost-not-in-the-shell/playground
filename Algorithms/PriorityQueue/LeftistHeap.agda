open import Algorithms.TotalOrder
module Algorithms.PriorityQueue.LeftistHeap {𝑘 ℓ 𝑣} (⟨Key,≤⟩ : TotalOrder 𝑘 ℓ) (Value : Set 𝑣) where
open TotalOrder ⟨Key,≤⟩ renaming (Carrier to Key)
open import Algorithms.PriorityQueue.Bounded ⟨Key,≤⟩ renaming (A⁺ to Key⁺)
open import Algorithms.Miscellaneous

mutual
  data Tree : Key⁺ → Set (𝑘 ⊔ ℓ ⊔ 𝑣) where
    leaf : Tree ∞
    node : ∀ {kˡ kʳ} (k : Key) (v : Value)
      → (tˡ : Tree kˡ) → k ⁺ ≤⁺ kˡ
      → (tʳ : Tree kʳ) → k ⁺ ≤⁺ kʳ
      → rank tˡ ≥ℕ rank tʳ
      → Tree (k ⁺)

  rank : ∀ {k} → Tree k → ℕ
  rank leaf = 0
  rank (node _ _ _ _ tʳ _ _) = suc (rank tʳ)

makeT : ∀ {k₁ k₂} (k : Key) (v : Value)
  → Tree k₁ → k ⁺ ≤⁺ k₁
  → Tree k₂ → k ⁺ ≤⁺ k₂
  → Tree (k ⁺)
makeT k v t₁ k≤k₁ t₂ k≤k₂ with ≥ℕ-total (rank t₁) (rank t₂)
... | inj₁ p = node k v t₁ k≤k₁ t₂ k≤k₂ p
... | inj₂ p = node k v t₂ k≤k₂ t₁ k≤k₁ p

merge : ∀ {k₁ k₂} → Tree k₁ → Tree k₂ → Tree (min⁺ k₁ k₂)
merge leaf leaf = leaf
merge leaf t@(node _ _ _ _ _ _ _) = t
merge t@(node _ _ _ _ _ _ _) leaf = t
merge t₁@(node k₁ v₁ l₁ ≤l₁ r₁ ≤r₁ _) t₂@(node k₂ v₂ l₂ ≤l₂ r₂ ≤r₂ _) with total k₁ k₂
... | inj₁ k₁≤k₂ = makeT k₁ v₁ l₁ ≤l₁ (merge r₁ t₂) ⟨ ≤r₁ , k₁≤k₂ ⁺ ⟩⁺
... | inj₂ k₂≤k₁ = makeT k₂ v₂ l₂ ≤l₂ (merge t₁ r₂) ⟨ k₂≤k₁ ⁺ , ≤r₂ ⟩⁺

insert : ∀ {k′} (k : Key) (v : Value) → Tree k′ → Tree (min⁺ (k ⁺) k′)
insert k v t = merge (node k v leaf ∞ leaf ∞ zero) t

findMin : ∀ {k} → Tree k → Key⁺
findMin {k} _ = k

deleteMin : ∀ {k} → Tree k → ∃ λ k′ → Tree k′
deleteMin leaf = _ , leaf
deleteMin (node k v l _ r _ _) = _ , merge l r
