module Prelude.Op where

record CategoricalOp {ob : Set} (hom : ob → ob → Set) : Set where
  infixr 5 _∘_
  field
    id  : ∀ {A} → hom A A
    _∘_ : ∀ {A B C} → hom B C → hom A B → hom A C

  id₍_₎ : ∀ A → hom A A
  id₍ A ₎ = id

open CategoricalOp ⦃...⦄ public

{-# DISPLAY CategoricalOp.id    _ = id    #-}
{-# DISPLAY CategoricalOp.id₍_₎ _ = id₍_₎ #-}
{-# DISPLAY CategoricalOp._∘_   _ = _∘_   #-}

record TerminalOp {ob : Set} (hom : ob → ob → Set) : Set where
  field
    𝟙 : ob

    ! : ∀ {X} → hom X 𝟙

  !₍_₎ : ∀ X → hom X 𝟙
  !₍ X ₎ = ! {X}

open TerminalOp ⦃...⦄ public

{-# DISPLAY TerminalOp.𝟙    _ = 𝟙    #-}
{-# DISPLAY TerminalOp.!    _ = !    #-}
{-# DISPLAY TerminalOp.!₍_₎ _ = !₍_₎ #-}

record ProductOp {ob : Set} (hom : ob → ob → Set) : Set where
  infixr 5 _×_
  field
    _×_ : ob → ob → ob

    π₁ : ∀ {A B} → hom (A × B) A
    π₂ : ∀ {A B} → hom (A × B) B
    ⟨_,_⟩ : ∀ {A B X} → hom X A → hom X B → hom X (A × B)

  π₁₍_,_₎ : ∀ A B → hom (A × B) A
  π₁₍ A , B ₎ = π₁ {A} {B}

  π₂₍_,_₎ : ∀ A B → hom (A × B) B
  π₂₍ A , B ₎ = π₂ {A} {B}

open ProductOp ⦃...⦄ public

{-# DISPLAY ProductOp._×_     _ = _×_     #-}
{-# DISPLAY ProductOp.π₁      _ = π₁      #-}
{-# DISPLAY ProductOp.π₂      _ = π₂      #-}
{-# DISPLAY ProductOp.π₁₍_,_₎ _ = π₁₍_,_₎ #-}
{-# DISPLAY ProductOp.π₂₍_,_₎ _ = π₂₍_,_₎ #-}
{-# DISPLAY ProductOp.⟨_,_⟩   _ = ⟨_,_⟩   #-}
