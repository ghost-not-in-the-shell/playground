module Diagram.Pullback 𝓒 where
open import Prelude
open import Category.Base

record is-pullback {I A B A⊗B}
  (a : 𝓒 ⦅ A   , I ⦆) (b : 𝓒 ⦅ B   , I ⦆)
  (p : 𝓒 ⦅ A⊗B , A ⦆) (q : 𝓒 ⦅ A⊗B , B ⦆) : Type where
  field
    square : a ∘ p ≡ b ∘ q
    mediate : ∀ {X} (f : 𝓒 ⦅ X , A ⦆) (g : 𝓒 ⦅ X , B ⦆) (□ : a ∘ f ≡ b ∘ g)
      → 𝓒 ⦅ X , A⊗B ⦆
  syntax mediate f g □ = < f [ □ ] g >′
  field
    commute₁ : ∀ {X} {f : 𝓒 ⦅ X , A ⦆} {g : 𝓒 ⦅ X , B ⦆} {□ : a ∘ f ≡ b ∘ g}
      → p ∘ < f [ □ ] g >′ ≡ f
    commute₂ : ∀ {X} {f : 𝓒 ⦅ X , A ⦆} {g : 𝓒 ⦅ X , B ⦆} {□ : a ∘ f ≡ b ∘ g}
      → q ∘ < f [ □ ] g >′ ≡ g
    unique : ∀ {X} {f : 𝓒 ⦅ X , A ⦆} {g : 𝓒 ⦅ X , B ⦆} {□ : a ∘ f ≡ b ∘ g}
      → {⁇ : 𝓒 ⦅ X , A⊗B ⦆}
      → (⁇-commute₁ : p ∘ ⁇ ≡ f)
      → (⁇-commute₂ : q ∘ ⁇ ≡ g)
      → ⁇ ≡ < f [ □ ] g >′

  unique₂ : ∀ {X} {f : 𝓒 ⦅ X , A ⦆} {g : 𝓒 ⦅ X , B ⦆} {□ : a ∘ f ≡ b ∘ g}
    → {⁇₁ ⁇₂ : 𝓒 ⦅ X , A⊗B ⦆}
    → (⁇₁-commute₁ : p ∘ ⁇₁ ≡ f) (⁇₁-commute₂ : q ∘ ⁇₁ ≡ g)
    → (⁇₂-commute₁ : p ∘ ⁇₂ ≡ f) (⁇₂-commute₂ : q ∘ ⁇₂ ≡ g)
    → ⁇₁ ≡ ⁇₂
  unique₂ {□ = □} ⁇₁-commute₁ ⁇₁-commute₂ ⁇₂-commute₁ ⁇₂-commute₂ =
    trans (unique {□ = □} ⁇₁-commute₁ ⁇₁-commute₂)
    $ sym (unique {□ = □} ⁇₂-commute₁ ⁇₂-commute₂)

record Pullback {I A B} (a : 𝓒 ⦅ A , I ⦆) (b : 𝓒 ⦅ B , I ⦆) : Type where
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

instance
  pullbackOp : ⦃ _ : Pullbacks ⦄ → PullbackOp (Hom 𝓒)
  pullbackOp ⦃ pullback-instance pull ⦄ = record
    { ⊗₍₎   = λ A B  a   b  → apex    (pull a b) 
    ; p     = λ {a = a} {b} → p       (pull a b)
    ; q     = λ {a = a} {b} → q       (pull a b)
    ; <[-]> = λ {a = a} {b} → mediate (pull a b)
    } where open Pullback

module ⊗ ⦃ (pullback-instance pull) : Pullbacks ⦄ where
  module _ {I A B} {a : 𝓒 ⦅ A , I ⦆} {b : 𝓒 ⦅ B , I ⦆} where
    open Pullback (pull a b) public hiding (apex; p; q)
