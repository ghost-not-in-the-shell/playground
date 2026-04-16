module Prelude.Idiom.Categorical where
open import Prelude.Prim

module _ {Ob : Type} where
  record CompositionalOp (Hom : Ob → Ob → Type) : Type where
    infixr 5 _∘_
    field
      id  : ∀ {A} → Hom A A
      _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C

    id₍_₎ : ∀ A → Hom A A
    id₍ A ₎ = id {A}

  open CompositionalOp ⦃...⦄ public

  record TerminalOp (Hom : Ob → Ob → Type) : Type where
    field
      𝟙 : Ob
      ! : ∀ {X} → Hom X 𝟙

  open TerminalOp ⦃...⦄ public

  {-# DISPLAY TerminalOp.𝟙 _ = 𝟙 #-}
  {-# DISPLAY TerminalOp.! _ = ! #-}

  record ProductOp (Hom : Ob → Ob → Type) : Type where
    infixr 7 _×_ _×₁_
    field
      _×_ : Ob → Ob → Ob
      π₁ : ∀ {A B} → Hom (A × B) A
      π₂ : ∀ {A B} → Hom (A × B) B
      <_,_> : ∀ {A B X} → Hom X A → Hom X B → Hom X (A × B)

    swap : ∀ {A B} → Hom (A × B) (B × A)
    swap = < π₂ , π₁ >

    _×₁_ : ∀ {A₁ A₂ B₁ B₂} ⦃ _ : CompositionalOp Hom ⦄
      → Hom A₁ B₁ → Hom A₂ B₂ → Hom (A₁ × A₂) (B₁ × B₂)
    f ×₁ g = < f ∘ π₁ , g ∘ π₂ >

  open ProductOp ⦃...⦄ public

  {-# DISPLAY ProductOp._×_   _ = _×_   #-}
  {-# DISPLAY ProductOp.π₁    _ = π₁    #-}
  {-# DISPLAY ProductOp.π₂    _ = π₂    #-}
  {-# DISPLAY ProductOp.<_,_> _ = <_,_> #-}
  {-# DISPLAY ProductOp.swap  _ = swap  #-}
  {-# DISPLAY ProductOp._×₁_  _ = _×₁_  #-}

  record PullbackOp (Hom : Ob → Ob → Type) ⦃ _ : CompositionalOp Hom ⦄ : Type where
    infixr 7 ⊗₍₎
    field
      ⊗₍₎ : ∀ {I} A B (a : Hom A I) (b : Hom B I) → Ob
    syntax ⊗₍₎ A B a b = A ⊗₍ a , b ₎ B
    field
      p : ∀ {I A B} {a : Hom A I} {b : Hom B I} → Hom (A ⊗₍ a , b ₎ B) A
      q : ∀ {I A B} {a : Hom A I} {b : Hom B I} → Hom (A ⊗₍ a , b ₎ B) B
      <[]> : ∀ {I A B X} {a : Hom A I} {b : Hom B I}
        → (f : Hom X A) (g : Hom X B)
        → (□ : a ∘ f ≡ b ∘ g)
        → Hom X (A ⊗₍ a , b ₎ B)

    syntax <[]> f g □ = < f [ □ ] g >
    
    p₍_,_₎ : ∀ {I A B} (a : Hom A I) (b : Hom B I) → Hom (A ⊗₍ a , b ₎ B) A
    q₍_,_₎ : ∀ {I A B} (a : Hom A I) (b : Hom B I) → Hom (A ⊗₍ a , b ₎ B) B
    p₍ _ , _ ₎ = p
    q₍ _ , _ ₎ = q

  open PullbackOp ⦃...⦄ public

  {-# DISPLAY PullbackOp.⊗₍₎    _ = ⊗₍₎    #-}
  {-# DISPLAY PullbackOp.p      _ = p      #-}
  {-# DISPLAY PullbackOp.q      _ = q      #-}
  {-# DISPLAY PullbackOp.<[]>   _ = <[]>   #-}
  {-# DISPLAY PullbackOp.p₍_,_₎ _ = p₍_,_₎ #-}
  {-# DISPLAY PullbackOp.q₍_,_₎ _ = q₍_,_₎ #-}

  record ExponentialOp (Hom : Ob → Ob → Type) ⦃ _ : ProductOp Hom ⦄ : Type where
    infixr 5 _⇒_
    field
      _⇒_ : Ob → Ob → Ob
      ev  : ∀ {A B} → Hom ((A ⇒ B) × A) B
      lam : ∀ {Γ A B} (f : Hom (Γ × A) B) → Hom Γ (A ⇒ B)

    app : ∀ ⦃ _ : CompositionalOp Hom ⦄ {Γ A B} (f : Hom Γ (A ⇒ B)) (x : Hom Γ A) → Hom Γ B
    app f x = ev ∘ < f , x >

  open ExponentialOp ⦃...⦄ public

{-# DISPLAY CompositionalOp.id    _ = id    #-}
{-# DISPLAY CompositionalOp._∘_   _ = _∘_   #-}
{-# DISPLAY CompositionalOp.id₍_₎ _ = id₍_₎ #-}  

{-# DISPLAY TerminalOp.𝟙 _ = 𝟙 #-}
{-# DISPLAY TerminalOp.! _ = ! #-}

{-# DISPLAY ProductOp._×_   _ = _×_   #-}
{-# DISPLAY ProductOp.π₁    _ = π₁    #-}
{-# DISPLAY ProductOp.π₂    _ = π₂    #-}
{-# DISPLAY ProductOp.<_,_> _ = <_,_> #-}
{-# DISPLAY ProductOp.swap  _ = swap  #-}
{-# DISPLAY ProductOp._×₁_  _ = _×₁_  #-}

{-# DISPLAY PullbackOp.⊗₍₎    _ = ⊗₍₎    #-}
{-# DISPLAY PullbackOp.p      _ = p      #-}
{-# DISPLAY PullbackOp.q      _ = q      #-}
{-# DISPLAY PullbackOp.<[]>   _ = <[]>   #-}
{-# DISPLAY PullbackOp.p₍_,_₎ _ = p₍_,_₎ #-}
{-# DISPLAY PullbackOp.q₍_,_₎ _ = q₍_,_₎ #-}

{-# DISPLAY ExponentialOp._⇒_ _ = _⇒_ #-}
{-# DISPLAY ExponentialOp.ev  _ = ev  #-}
{-# DISPLAY ExponentialOp.lam _ = lam #-}
{-# DISPLAY ExponentialOp.app _ = app #-}

record Opposite (A : Type) (Aᵒᵖ : Type) : Type where
  infix 5 opposite
  field
    opposite : A → Aᵒᵖ

open Opposite ⦃...⦄ public renaming (opposite to _ᵒᵖ)

{-# DISPLAY Opposite.opposite _ = _ᵒᵖ #-}

record is-iso {Ob : Type} (Hom : Ob → Ob → Type) ⦃ _ : CompositionalOp Hom ⦄ {A B : Ob} (f : Hom A B) : Type where
  field
    bwd : Hom B A
  private
    f⁻¹ = bwd
  field
    ∘-invˡ : f⁻¹ ∘ f ≡ id
    ∘-invʳ : f ∘ f⁻¹ ≡ id

module _ {Ob : Type} {Hom : Ob → Ob → Type} ⦃ _ : CompositionalOp Hom ⦄ {A B : Ob} (f : Hom A B) ⦃ iso : is-iso Hom f ⦄ where
  infix 5 _⁻¹
  _⁻¹ = is-iso.bwd iso
  ∘-invˡ = is-iso.∘-invˡ iso
  ∘-invʳ = is-iso.∘-invʳ iso

{-# DISPLAY is-iso.bwd {f = f} _ = f ⁻¹ #-}

Function : Type → Type → Type
Function A B = A → B

instance
  Type-compositionalOp : CompositionalOp Function
  Type-compositionalOp = record
    { id  = λ x → x
    ; _∘_ = λ g f x → g (f x)
    }

  Type-productOp : ProductOp Function
  Type-productOp = record
    { _×_ = λ A B → Σ A (λ _ → B)
    ; π₁ = fst
    ; π₂ = snd
    ; <_,_> = λ f g x → f x , g x
    }
    
record _≅_ (A B : Type) : Type where
  constructor fwd
  field
    fwd : A → B
    ⦃ iso ⦄ : is-iso Function fwd
