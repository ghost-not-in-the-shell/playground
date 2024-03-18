module Prelude.Op where

record CategoricalOp {Ob : Set} (Hom : Ob → Ob → Set) : Set where
  infixr 5 _∘_
  field
    id  : ∀ {A} → Hom A A
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C

  id₍_₎ : ∀ A → Hom A A
  id₍ A ₎ = id

open CategoricalOp ⦃...⦄ public

{-# DISPLAY CategoricalOp.id    _ = id    #-}
{-# DISPLAY CategoricalOp.id₍_₎ _ = id₍_₎ #-}
{-# DISPLAY CategoricalOp._∘_   _ = _∘_   #-}

record InitialOp {Ob : Set} (Hom : Ob → Ob → Set) : Set where
  field
    𝟘 : Ob

    ¡ : ∀ {X} → Hom 𝟘 X

  ¡₍_₎ : ∀ X → Hom 𝟘 X
  ¡₍ X ₎ = ¡ {X}

open InitialOp ⦃...⦄ public

{-# DISPLAY InitialOp.𝟘    _ = 𝟘    #-}
{-# DISPLAY InitialOp.¡    _ = ¡    #-}
{-# DISPLAY InitialOp.¡₍_₎ _ = ¡₍_₎ #-}

record TerminalOp {Ob : Set} (Hom : Ob → Ob → Set) : Set where
  field
    𝟙 : Ob

    ! : ∀ {X} → Hom X 𝟙

  !₍_₎ : ∀ X → Hom X 𝟙
  !₍ X ₎ = ! {X}

open TerminalOp ⦃...⦄ public

{-# DISPLAY TerminalOp.𝟙    _ = 𝟙    #-}
{-# DISPLAY TerminalOp.!    _ = !    #-}
{-# DISPLAY TerminalOp.!₍_₎ _ = !₍_₎ #-}

record ProductOp {Ob : Set} (Hom : Ob → Ob → Set) : Set where
  infixr 6 _×_ _×₁_
  field
    _×_ : Ob → Ob → Ob

    π₁ : ∀ {A B} → Hom (A × B) A
    π₂ : ∀ {A B} → Hom (A × B) B
    <_,_> : ∀ {A B X} → Hom X A → Hom X B → Hom X (A × B)

  π₁₍_,_₎ : ∀ A B → Hom (A × B) A
  π₁₍ A , B ₎ = π₁ {A} {B}

  π₂₍_,_₎ : ∀ A B → Hom (A × B) B
  π₂₍ A , B ₎ = π₂ {A} {B}

  _×₁_ : ∀ ⦃ _ : CategoricalOp Hom ⦄ {A₁ A₂ B₁ B₂} → Hom A₁ B₁ → Hom A₂ B₂ → Hom (A₁ × A₂) (B₁ × B₂)
  f ×₁ g = < f ∘ π₁ , g ∘ π₂ >

open ProductOp ⦃...⦄ public

{-# DISPLAY ProductOp._×_     _ = _×_     #-}
{-# DISPLAY ProductOp.π₁      _ = π₁      #-}
{-# DISPLAY ProductOp.π₂      _ = π₂      #-}
{-# DISPLAY ProductOp.π₁₍_,_₎ _ = π₁₍_,_₎ #-}
{-# DISPLAY ProductOp.π₂₍_,_₎ _ = π₂₍_,_₎ #-}
{-# DISPLAY ProductOp.<_,_>   _ = <_,_>   #-}
{-# DISPLAY ProductOp._×₁_    _ = _×₁_    #-}

record CoproductOp {Ob : Set} (Hom : Ob → Ob → Set) : Set where
  infixr 5 _+_ _+₁_
  field
    _+_ : Ob → Ob → Ob

    inj₁ : ∀ {A B} → Hom A (A + B)
    inj₂ : ∀ {A B} → Hom B (A + B)
    [_,_] : ∀ {A B X} → Hom A X → Hom B X → Hom (A + B) X

  _+₁_ : ∀ ⦃ _ : CategoricalOp Hom ⦄ {A₁ A₂ B₁ B₂} → Hom A₁ B₁ → Hom A₂ B₂ → Hom (A₁ + A₂) (B₁ + B₂)
  f +₁ g = [ inj₁ ∘ f , inj₂ ∘ g ]

open CoproductOp ⦃...⦄ public

{-# DISPLAY CoproductOp._+_   _ = _+_   #-}
{-# DISPLAY CoproductOp.inj₁  _ = inj₁  #-}
{-# DISPLAY CoproductOp.inj₂  _ = inj₂  #-}
{-# DISPLAY CoproductOp.[_,_] _ = [_,_] #-}
{-# DISPLAY CoproductOp._+₁_  _ = _+₁_  #-}
