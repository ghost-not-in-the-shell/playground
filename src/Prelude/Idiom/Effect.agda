{-# OPTIONS --type-in-type #-}
module Prelude.Idiom.Effect where
open import Agda.Primitive
open import Prelude.Bool
open import Prelude.Function
open import Prelude.Unit
open import Prelude.Idiom.Category

Effect = Set → Set

private
  variable
    A B : Set

record Map (F : Effect) : Set where
  field
    map : (A → B) → F A → F B

  infixl 4 _<$>_
  _<$>_ : (A → B) → F A → F B
  _<$>_ = map

record Applicative (F : Effect) : Set where
  infixl 4 _<*>_ _<*_ _*>_
  field
    pure  : A → F A
    _<*>_ : F (A → B) → F A → F B

  functor : Map F
  functor = record { map = λ f x → pure f <*> x }

  open Map functor

  _<*_ : F A → F B → F A
  a <* b = const <$> a <*> b

  _*>_ : F A → F B → F B
  a *> b = flip const <$> a <*> b

record Bind (M : Effect) : Set where
  infixl 1 _>>=_ _>>_
  field
    return : A → M A
    _>>=_  : M A → (A → M B) → M B

  applicative : Applicative M
  applicative = record
    { pure  = return
    ; _<*>_ = λ mf ma → do
      f ← mf
      a ← ma
      return $ f a
    }

  open Applicative applicative

  _>>_ : M A → M B → M B
  _>>_ = _*>_

open Map         ⦃ ... ⦄ public
open Applicative ⦃ ... ⦄ public
open Bind        ⦃ ... ⦄ public

record Alt (F : Effect) : Set where
  infixl 3 _<|>_
  field
    fail  : F A
    _<|>_ : F A → F A → F A

  guard : ⦃ _ : Applicative F ⦄ → Bool → F ⊤
  guard true  = pure tt
  guard false = fail

  guardM : ⦃ _ : Applicative F ⦄ ⦃ _ : Bind F ⦄ → F Bool → F ⊤
  guardM m = m >>= guard

open Alt ⦃ ... ⦄ public

record Traversable (T : Effect) : Set where
  field
    traverse : {F : Effect} ⦃ _ : Applicative F ⦄
      → (A → F B) → T A → F (T B)

  sequence : ∀ {F : Effect} ⦃ _ : Applicative F ⦄
    → T (F A) → F (T A)
  sequence = traverse id

open Traversable ⦃ ... ⦄ public
