module Limit.Instances.Pullback where
open import Prelude
open import Category.Base

module _ 𝓒 where
  record is-pullback {I A B a⊗b}
      (a : 𝓒 ⦅ A   , I ⦆) (b : 𝓒 ⦅ B   , I ⦆)
      (p : 𝓒 ⦅ a⊗b , A ⦆) (q : 𝓒 ⦅ a⊗b , B ⦆) : Type where
    no-eta-equality
    field
      square : a ∘ p ≡ b ∘ q
      mediate : ∀ {X} (f : 𝓒 ⦅ X , A ⦆) (g : 𝓒 ⦅ X , B ⦆) (□ : a ∘ f ≡ b ∘ g)
        → 𝓒 ⦅ X , a⊗b ⦆
    syntax mediate f g □ = < f [ □ ] g >′
    <_□_>′ : ∀ {X} (f : 𝓒 ⦅ X , A ⦆) (g : 𝓒 ⦅ X , B ⦆) {□ : a ∘ f ≡ b ∘ g}
      → 𝓒 ⦅ X , a⊗b ⦆
    <_□_>′ f g {□} = < f [ □ ] g >′
    field
      commute₁ : ∀ {X} {f : 𝓒 ⦅ X , A ⦆} {g : 𝓒 ⦅ X , B ⦆} {□ : a ∘ f ≡ b ∘ g}
        → p ∘ < f [ □ ] g >′ ≡ f
      commute₂ : ∀ {X} {f : 𝓒 ⦅ X , A ⦆} {g : 𝓒 ⦅ X , B ⦆} {□ : a ∘ f ≡ b ∘ g}
        → q ∘ < f [ □ ] g >′ ≡ g
      unique : ∀ {X} {f : 𝓒 ⦅ X , A ⦆} {g : 𝓒 ⦅ X , B ⦆} {□ : a ∘ f ≡ b ∘ g}
        → {⁇ : 𝓒 ⦅ X , a⊗b ⦆}
        → (⁇-commute₁ : p ∘ ⁇ ≡ f)
        → (⁇-commute₂ : q ∘ ⁇ ≡ g)
        → ⁇ ≡ < f [ □ ] g >′

    unique₂ : ∀ {X} {f : 𝓒 ⦅ X , A ⦆} {g : 𝓒 ⦅ X , B ⦆} {□ : a ∘ f ≡ b ∘ g}
      → {⁇₁ ⁇₂ : 𝓒 ⦅ X , a⊗b ⦆}
      → (⁇₁-commute₁ : p ∘ ⁇₁ ≡ f) (⁇₁-commute₂ : q ∘ ⁇₁ ≡ g)
      → (⁇₂-commute₁ : p ∘ ⁇₂ ≡ f) (⁇₂-commute₂ : q ∘ ⁇₂ ≡ g)
      → ⁇₁ ≡ ⁇₂
    unique₂ {□ = □} ⁇₁-commute₁ ⁇₁-commute₂ ⁇₂-commute₁ ⁇₂-commute₂ =
      trans (unique {□ = □} ⁇₁-commute₁ ⁇₁-commute₂)
      $ sym (unique {□ = □} ⁇₂-commute₁ ⁇₂-commute₂)

  record Pullback {I A B} (a : 𝓒 ⦅ A , I ⦆) (b : 𝓒 ⦅ B , I ⦆) : Type where
    no-eta-equality
    field
      apex : Ob 𝓒
      p : 𝓒 ⦅ apex , A ⦆
      q : 𝓒 ⦅ apex , B ⦆
      pullback : is-pullback a b p q

    open is-pullback pullback public

  record Pullbacks : Type where
    constructor pullback-instance
    field
      has-all-pullbacks : ∀ {I A B} (a : 𝓒 ⦅ A , I ⦆) (b : 𝓒 ⦅ B , I ⦆) → Pullback a b

  module ⊗ ⦃ (pullback-instance pull) : Pullbacks ⦄ where
    module _ {I A B} {a : 𝓒 ⦅ A , I ⦆} {b : 𝓒 ⦅ B , I ⦆} where
      open Pullback (pull a b) public hiding (apex; p; q)

    instance
      pullbackOp : PullbackOp (Hom 𝓒)
      pullbackOp = record
        { _⊗_   = λ {I A B}  a b  → pull a b .apex
        ; p     = λ {I A B   a b} → pull a b .p
        ; q     = λ {I A B   a b} → pull a b .q
        ; <[-]> = λ {I A B X a b} → pull a b .mediate
        } where open Pullback

{-# DISPLAY Pullbacks.has-all-pullbacks _ a b .Pullback.apex = a ⊗ b #-}
{-# DISPLAY Pullback.p _ = p #-}
{-# DISPLAY Pullback.q _ = q #-}
{-# DISPLAY is-pullback.mediate _ f g _ = < f □ g > #-}

module _ {𝓒} ⦃ _ : Pullbacks 𝓒 ⦄ where
  open import Category.Instances.Slice
  open import Functor.Base

  private instance
    _ = ⊗.pullbackOp 𝓒

  _* : ∀ {I J} (u : 𝓒 ᵒᵖ ⦅ I , J ⦆) → 𝓒 / I ⟶ 𝓒 / J
  _* {I} {J} u = record
    { map₀ = λ (A , a) → u ⊗ a , p
    ; map₁ = λ {(A , a) (B , b)} (f , f-vertical) →
      let □ : u ∘ p ≡ b ∘ (f ∘ q)
          □ = begin
            u     ∘ p ≡⟨ ⊗.square 𝓒 ⟩
            a     ∘ q ≡⟨ f-vertical ○ - ⟩
           (b ∘ f)∘ q ≡⟨ ∘-assoc 𝓒 ⟩
            b ∘(f ∘ q) ∎
      in record
        { morphism = < p [ □ ] f ∘ q >
        ; vertical = sym (⊗.commute₁ 𝓒)
        }
    ; resp-id = ext $ sym $ ⊗.unique 𝓒 (∘-idʳ 𝓒) (sym (∘-idˡʳ 𝓒))
    ; resp-∘ = λ {(A , a) (B , b) (C , c) (f , f-vertical) (g , g-vertical)} →
        ext $ sym $ ⊗.unique 𝓒
          (begin
            p ∘(< p □ g ∘ q > ∘ < p □ f ∘ q >) ≡⟨ ∘-assoc 𝓒 ⟨
           (p ∘ < p □ g ∘ q >)∘ < p □ f ∘ q >  ≡⟨ ⊗.commute₁ 𝓒 ○ - ⟩
                  p           ∘ < p □ f ∘ q >  ≡⟨ ⊗.commute₁ 𝓒 ⟩
                                  p            ∎)
          (begin
            q ∘(< p □ g ∘ q > ∘ < p □ f ∘ q >) ≡⟨ ∘-assoc 𝓒 ⟨
           (q ∘ < p □ g ∘ q >)∘ < p □ f ∘ q >  ≡⟨ ⊗.commute₂ 𝓒 ○ - ⟩
                     (g ∘ q)  ∘ < p □ f ∘ q >  ≡⟨ ∘-assoc 𝓒 ⟩
                      g ∘(q   ∘ < p □ f ∘ q >) ≡⟨ - ○ ⊗.commute₂ 𝓒 ⟩
                      g ∘            (f ∘ q)   ≡⟨ ∘-assoc 𝓒 ⟨
                     (g ∘             f)∘ q    ∎)
    }
