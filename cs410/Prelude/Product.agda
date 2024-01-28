{-# OPTIONS --type-in-type #-}
module Prelude.Product where
open import Prelude.Function
open import Prelude.Op

infixr 4 _,_
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

infixr 4 -,_
pattern -,_ y = _ , y

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ = Σ _

infix 2 ∃-syntax
∃-syntax : ∀ {A : Set} (B : A → Set) → Set
∃-syntax = Σ _

syntax ∃-syntax (λ x → B) = ∃[ x ] B

instance
  𝓢𝓮𝓽-product : ProductOp Function
  𝓢𝓮𝓽-product = record
    { _×_   = λ A B → Σ A $ const B
    ; π₁    = fst
    ; π₂    = snd
    ; <_,_> = λ f g x → f x , g x
    }
