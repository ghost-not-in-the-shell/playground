module Prelude.Idiom.Category where

record Categorical {Ob : Set} (Hom : Ob → Ob → Set) : Set where
  infixr 5 _∘_
  field
    id  : ∀ {A} → Hom A A
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C

  id₍_₎ : ∀ A → Hom A A
  id₍ A ₎ = id {A}

open Categorical ⦃ ... ⦄ public

{-# DISPLAY Categorical.id  _     = id    #-}
{-# DISPLAY Categorical._∘_ _ g f = g ∘ f #-}

record Cartesian {Ob : Set} (Hom : Ob → Ob → Set) : Set where
  infixr 5 _×_
  infixr 6 _×₁_
  field
    _×_ : Ob → Ob → Ob

    π₁ : ∀ {A B} → Hom (A × B) A
    π₂ : ∀ {A B} → Hom (A × B) B
    <_,_> : ∀ {A B X} → Hom X A → Hom X B → Hom X (A × B)

  _×₁_ : ∀ ⦃ _ : Categorical Hom ⦄ {A B C D} → Hom A B → Hom C D → Hom (A × C) (B × D)
  f ×₁ g = < f ∘ π₁ , g ∘ π₂ >

open Cartesian ⦃ ... ⦄ public
