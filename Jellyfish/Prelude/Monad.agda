module Jellyfish.Prelude.Monad where
open import Agda.Primitive

record Functor {𝔞 𝔟} (F : Set 𝔞 → Set 𝔟) : Set (lsuc 𝔞 ⊔ 𝔟) where
  infixl 4 _<$>_
  field
    _<$>_ : ∀ {A B} → (A → B) → F A → F B

open Functor ⦃...⦄ public

{-# DISPLAY Functor._<$>_ _ = _<$>_ #-}

record Applicative {𝔞 𝔟} (F : Set 𝔞 → Set 𝔟) : Set (lsuc 𝔞 ⊔ 𝔟) where
  infixl 4 _<*>_
  field
    pure : ∀ {A} → A → F A
    _<*>_ : ∀ {A B} → F (A → B) → F A → F B
    overlap ⦃ functor ⦄ : Functor F

open Applicative ⦃...⦄ public

{-# DISPLAY Applicative.pure  _ = pure  #-}
{-# DISPLAY Applicative._<*>_ _ = _<*>_ #-}

record Monad {𝔞 𝔟} (M : Set 𝔞 → Set 𝔟) : Set (lsuc 𝔞 ⊔ 𝔟) where
  infixl 1 _>>=_ _>>_
  field
    _>>=_ : ∀ {A B} → M A → (A → M B) → M B
    overlap ⦃ applicative ⦄ : Applicative M

  _>>_ : ∀ {A B} → M A → M B → M B
  m₁ >> m₂ = m₁ >>= λ _ → m₂

open Monad ⦃...⦄ public

{-# DISPLAY Monad._>>=_  _ = _>>=_  #-}
{-# DISPLAY Monad._>>_   _ = _>>_   #-}

record FunctorZero {𝔞 𝔟} (F : Set 𝔞 → Set 𝔟) : Set (lsuc 𝔞 ⊔ 𝔟) where
  field
    empty : ∀ {A} → F A
    overlap ⦃ functor ⦄ : Functor F

open FunctorZero ⦃...⦄ public

{-# DISPLAY FunctorZero.empty _ = empty #-}

record Alternative {𝔞 𝔟} (F : Set 𝔞 → Set 𝔟) : Set (lsuc 𝔞 ⊔ 𝔟) where
  infixl 3 _<|>_
  field
    _<|>_ : ∀ {A} → F A → F A → F A
    overlap ⦃ functor-zero ⦄ : FunctorZero F

open Alternative ⦃...⦄ public

{-# DISPLAY Alternative._<|>_ _ = _<|>_ #-}
