open import Algorithms.StrictTotalOrder
module Algorithms.OrderedCollection.Bounded {𝑎 ℓ} (⟨A,<⟩ : StrictTotalOrder 𝑎 ℓ) where
open StrictTotalOrder ⟨A,<⟩ renaming (Carrier to A)
open import Algorithms.Equality
open import Algorithms.Miscellaneous

infix 4 _<⁺_
infix 7 _⁻

data A⁺ : Set 𝑎 where
  -∞ : A⁺
  +∞ : A⁺
  _⁺ : A → A⁺

_⁻ : ∀ {x y} → x ⁺ ≡ y ⁺ → x ≡ y
refl ⁻ = refl

data _<⁺_ : A⁺ → A⁺ → Set ℓ where
  -∞ : ∀ {x}           → -∞  <⁺ x ⁺
  +∞ : ∀ {x}           → x ⁺ <⁺ +∞
  ∞  :                   -∞  <⁺ +∞
  _⁺ : ∀ {x y} → x < y → x ⁺ <⁺ y ⁺

pattern ∞̸ = _ ⁺

_⁻̂ : ∀ {x y} → x ⁺ <⁺ y ⁺ → x < y
(p ⁺)⁻̂ = p

trans⁺ : ∀ {x⁺ y⁺ z⁺} → x⁺ <⁺ y⁺ → y⁺ <⁺ z⁺ → x⁺ <⁺ z⁺
trans⁺ -∞   ∞̸ = -∞
trans⁺  ∞̸  +∞ = +∞
trans⁺ -∞  +∞ =  ∞
trans⁺ +∞  ()
trans⁺  ∞  ()
trans⁺ (p ⁺) (q ⁺) = (trans p q)⁺

compare⁺ : StrictTotal _<⁺_
compare⁺ -∞ -∞ = tri≡ (λ ()) refl   (λ ())
compare⁺ -∞  ∞̸ = tri< -∞     (λ ()) (λ ())
compare⁺ -∞ +∞ = tri<  ∞     (λ ()) (λ ())
compare⁺ +∞ -∞ = tri> (λ ()) (λ ())  ∞
compare⁺ +∞  ∞̸ = tri> (λ ()) (λ ()) +∞
compare⁺ +∞ +∞ = tri≡ (λ ()) refl   (λ ())
compare⁺  ∞̸ -∞ = tri> (λ ()) (λ ()) -∞
compare⁺  ∞̸ +∞ = tri< +∞     (λ ()) (λ ())
compare⁺ (x ⁺) (y ⁺) with compare x y
... | tri<  a ¬b ¬c = tri< (a ⁺)               (λ b⁺ → (b⁺)⁻ ↯ ¬b) (λ c⁺ → (c⁺)⁻̂ ↯ ¬c)
... | tri≡ ¬a  b ¬c = tri≡ (λ a⁺ → (a⁺)⁻̂ ↯ ¬a) (_⁺ ⟨$⟩ b)          (λ c⁺ → (c⁺)⁻̂ ↯ ¬c)
... | tri> ¬a ¬b  c = tri> (λ a⁺ → (a⁺)⁻̂ ↯ ¬a) (λ b⁺ → (b⁺)⁻ ↯ ¬b) (c ⁺)

⟨A⁺,<⁺⟩ : StrictTotalOrder 𝑎 ℓ
⟨A⁺,<⁺⟩ = record
  { Carrier = A⁺
  ; _<_     = _<⁺_
  ; trans   = trans⁺
  ; compare = compare⁺
  }

open StrictTotalOrder ⟨A⁺,<⁺⟩ renaming (_<_<_ to _<⁺_<⁺_) using () public
