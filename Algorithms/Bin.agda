module Algorithms.Bin where
open import Algorithms.Equality
open import Algorithms.Miscellaneous hiding (_+_)

data Bin : Set where
  ε   : Bin
  _◂𝟘 : Bin → Bin
  _◂𝟙 : Bin → Bin

incr : Bin → Bin
incr ε       = ε  ◂𝟙
incr (bs ◂𝟘) = bs ◂𝟙
incr (bs ◂𝟙) = (incr bs) ◂𝟘

toℕ : Bin → ℕ
toℕ ε       = zero
toℕ (bs ◂𝟘) =      (toℕ bs) * 2
toℕ (bs ◂𝟙) = suc ((toℕ bs) * 2)

fromℕ : ℕ → Bin
fromℕ zero    = ε
fromℕ (suc n) = incr (fromℕ n)

_+_ : Bin → Bin → Bin
ε   + bs₂ = bs₂
bs₁ + ε   = bs₁
(bs₁ ◂𝟘) + (bs₂ ◂𝟘) = (bs₁ + bs₂) ◂𝟘
(bs₁ ◂𝟘) + (bs₂ ◂𝟙) = (bs₁ + bs₂) ◂𝟙
(bs₁ ◂𝟙) + (bs₂ ◂𝟘) = (bs₁ + bs₂) ◂𝟙
(bs₁ ◂𝟙) + (bs₂ ◂𝟙) = incr (bs₁ + bs₂) ◂𝟘

_≪_ : Bin → ℕ → Bin
bs ≪ zero  = bs
bs ≪ suc n = (bs ◂𝟘) ≪ n

maskOff : Bin → ℕ → Bin
maskOff ε n = ε
maskOff (bs ◂𝟘) zero = bs ◂𝟘
maskOff (bs ◂𝟙) zero = bs ◂𝟘
maskOff (bs ◂𝟘) (suc n) = maskOff bs n ◂𝟘
maskOff (bs ◂𝟙) (suc n) = maskOff bs n ◂𝟙

incr≢ε : ∀ {bs} → ¬ incr bs ≡ ε
incr≢ε {ε}     = λ ()
incr≢ε {bs ◂𝟘} = λ ()
incr≢ε {bs ◂𝟙} = λ ()

+‿identityʳ : ∀ {bs} → bs + ε ≡ bs
+‿identityʳ {ε}     = refl
+‿identityʳ {bs ◂𝟘} = refl
+‿identityʳ {bs ◂𝟙} = refl
