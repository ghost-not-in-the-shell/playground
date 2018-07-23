open import Algorithms.TotalOrder
module Algorithms.PriorityQueue.BinomialHeap {𝑘 ℓ 𝑣} (⟨Key,≤⟩ : TotalOrder 𝑘 ℓ) (Value : Set 𝑣) where
open TotalOrder ⟨Key,≤⟩ renaming (Carrier to Key)
open import Algorithms.PriorityQueue.Bounded ⟨Key,≤⟩ renaming (A⁺ to Key⁺)
open import Algorithms.Bin
open import Algorithms.Equality
open import Algorithms.Miscellaneous hiding (_+_)

infixr 5 _∷_

mutual
  data List : ℕ → Set (𝑘 ⊔ 𝑣) where
    []  : List zero
    _∷_ : ∀ {n} → Tree n → List n → List (suc n)

  data Tree n : Set (𝑘 ⊔ 𝑣) where
    node : ∀ (k : Key) (v : Value)
      → List n
      → Tree n

link : ∀ {n}
  → Tree n
  → Tree n
  → Tree (suc n)
link t₁@(node k₁ v₁ ts₁) t₂@(node k₂ v₂ ts₂) with total k₁ k₂
... | inj₁ k₁≤k₂ = node k₁ v₁ (t₂ ∷ ts₁)
... | inj₂ k₂≤k₁ = node k₁ v₁ (t₁ ∷ ts₂)

data Heap n : Bin → Set (𝑘 ⊔ 𝑣) where
  ε    : Heap n ε
  _◂𝟘  : ∀ {bs} → Heap (suc n) bs → Heap n (bs ◂𝟘)
  _◂𝟙_ : ∀ {bs} → Heap (suc n) bs → Tree n → Heap n (bs ◂𝟙)

ins : ∀ {n bs} → Tree n → Heap n bs → Heap n (incr bs)
ins t₁ ε           = ε   ◂𝟙 t₁
ins t₁ (ts₂ ◂𝟘)    = ts₂ ◂𝟙 t₁
ins t₁ (ts₂ ◂𝟙 t₂) = ins (link t₁ t₂) ts₂ ◂𝟘

insert : ∀ {bs} Key → Value → Heap 0 bs → Heap 0 (incr bs)
insert k v ts = ins (node k v []) ts

merge : ∀ {n bs₁ bs₂} → Heap n bs₁ → Heap n bs₂ → Heap n (bs₁ + bs₂)
merge ε   ts₂ = ts₂
merge ts₁ ε   = ts₁ ⟦ Heap _ ⟨$⟩ sym +‿identityʳ ⟫
merge (ts₁ ◂𝟘)    (ts₂ ◂𝟘)    = merge ts₁ ts₂ ◂𝟘
merge (ts₁ ◂𝟘)    (ts₂ ◂𝟙 t₂) = merge ts₁ ts₂ ◂𝟙 t₂
merge (ts₁ ◂𝟙 t₁) (ts₂ ◂𝟘)    = merge ts₁ ts₂ ◂𝟙 t₁
merge (ts₁ ◂𝟙 t₁) (ts₂ ◂𝟙 t₂) = ins (link t₁ t₂) (merge ts₁ ts₂) ◂𝟘

removeMinTree : ∀ {n bs} → Heap n (incr bs) → ∃ λ m → Tree m × Heap n (maskOff (incr bs) m)
removeMinTree {bs = bs} t with incr bs
removeMinTree {bs = bs} t | ε = {!!}
removeMinTree {bs = bs} t | bs′ ◂𝟘 = {!!}
removeMinTree {bs = bs} t | bs′ ◂𝟙 = {!!}

