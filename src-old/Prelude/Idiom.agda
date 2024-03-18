{-# OPTIONS --type-in-type #-}
module Prelude.Idiom where

variable
  A B : Set

Effect = Set → Set

record Map (F : Effect) : Set where
  field
    map : (A → B) → F A → F B

record Idiom (F : Effect) : Set where
  infixl 4 _<*>_
  field
    pure  : A → F A
    _<*>_ : F (A → B) → F A → F B

open Map   ⦃ ... ⦄ public
open Idiom ⦃ ... ⦄ public

record Traversable (T : Effect) : Set where
  field
    traverse : ∀ {F} ⦃ _ : Idiom F ⦄
      → (A → F B) → T A → F (T B)

open Traversable ⦃ ... ⦄ public

record Bind (M : Effect) : Set where
  infixl 1 _>>=_
  field
    _>>=_ : M A → (A → M B) → M B

open Bind ⦃ ... ⦄ public
