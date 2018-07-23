module Algorithms.StrictTotalOrder where
open import Algorithms.Equality
open import Algorithms.Miscellaneous

data Tri {𝑎 𝑏 𝑐} (A : Set 𝑎) (B : Set 𝑏) (C : Set 𝑐) : Set (𝑎 ⊔ 𝑏 ⊔ 𝑐) where
  tri< : ( a :   A) (¬b : ¬ B) (¬c : ¬ C) → Tri A B C
  tri≡ : (¬a : ¬ A) ( b :   B) (¬c : ¬ C) → Tri A B C
  tri> : (¬a : ¬ A) (¬b : ¬ B) ( c :   C) → Tri A B C

pattern lt = tri< _ _ _
pattern eq = tri≡ _ _ _
pattern gt = tri> _ _ _

StrictTotal : ∀ {𝑎 ℓ} {A : Set 𝑎} → (A → A → Set ℓ) → Set _
StrictTotal _<_ = ∀ x y → Tri (x < y) (x ≡ y) (x > y)
  where _>_ = flip _<_

record StrictTotalOrder 𝑎 ℓ : Set (lsuc (𝑎 ⊔ ℓ)) where
  infix 4 _<_
  infix 4 _<_<_
  field
    Carrier : Set 𝑎
    _<_     : Carrier → Carrier → Set ℓ

    trans   : ∀ {x y z} → x < y → y < z → x < z
    compare : StrictTotal _<_

  _<_<_ : Carrier → Carrier → Carrier → Set ℓ
  x < y < z = (x < y) × (y < z)
