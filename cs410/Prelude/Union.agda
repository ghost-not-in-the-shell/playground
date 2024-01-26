{-# OPTIONS --type-in-type #-}
module Prelude.Union where
open import Prelude.Function
open import Prelude.Op

infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B

instance
  𝓢𝓮𝓽-coproduct : CoproductOp Function
  𝓢𝓮𝓽-coproduct = record
    { _+_   = _⊎_
    ; inj₁  = left
    ; inj₂  = right
    ; [_,_] = λ { f g (left  x) → f x
                ; f g (right y) → g y }
    }
