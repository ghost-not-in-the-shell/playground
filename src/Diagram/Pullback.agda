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

  <_[]_>′ : ∀ {X} (f : 𝓒 ⦅ X , A ⦆) (g : 𝓒 ⦅ X , B ⦆) {□ : a ∘ f ≡ b ∘ g}
    → 𝓒 ⦅ X , A⊗B ⦆
  <_[]_>′ f g {□} = < f [ □ ] g >′

  unique₂ : ∀ {X} {f : 𝓒 ⦅ X , A ⦆} {g : 𝓒 ⦅ X , B ⦆} {□ : a ∘ f ≡ b ∘ g}
    → {⁇₁ ⁇₂ : 𝓒 ⦅ X , A⊗B ⦆}
    → (⁇₁-commute₁ : p ∘ ⁇₁ ≡ f) (⁇₁-commute₂ : q ∘ ⁇₁ ≡ g)
    → (⁇₂-commute₁ : p ∘ ⁇₂ ≡ f) (⁇₂-commute₂ : q ∘ ⁇₂ ≡ g)
    → ⁇₁ ≡ ⁇₂
  unique₂ {□ = □} ⁇₁-commute₁ ⁇₁-commute₂ ⁇₂-commute₁ ⁇₂-commute₂ =
    trans (unique {□ = □} ⁇₁-commute₁ ⁇₁-commute₂)
    $ sym (unique {□ = □} ⁇₂-commute₁ ⁇₂-commute₂)

  <[]>∘ : ∀ {X Y} {f : 𝓒 ⦅ X , Y ⦆} {g₁ : 𝓒 ⦅ Y , A ⦆} {g₂ : 𝓒 ⦅ Y , B ⦆} {□ : a ∘ g₁ ≡ b ∘ g₂} {□′ : a ∘ (g₁ ∘ f) ≡ b ∘ (g₂ ∘ f)}
    → let □∘f : a ∘ (g₁ ∘ f) ≡ b ∘ (g₂ ∘ f)
          □∘f = begin
            a ∘(g₁ ∘ f) ≡⟨ ∘-assoc 𝓒 ⟨
           (a ∘ g₁)∘ f  ≡⟨ □ ○ - ⟩
           (b ∘ g₂)∘ f  ≡⟨ ∘-assoc 𝓒 ⟩
            b ∘(g₂ ∘ f) ∎
      in < g₁ [ □ ] g₂ >′ ∘ f ≡ < g₁ ∘ f [ □∘f ] g₂ ∘ f >′
  <[]>∘ {f = f} {g₁} {g₂} = unique
    (begin
      p ∘(< g₁ [] g₂ >′ ∘ f) ≡⟨ ∘-assoc 𝓒 ⟨
     (p ∘ < g₁ [] g₂ >′)∘ f  ≡⟨ commute₁ ○ - ⟩
            g₁          ∘ f  ∎)
    (begin
      q ∘(< g₁ [] g₂ >′ ∘ f) ≡⟨ ∘-assoc 𝓒 ⟨
     (q ∘ < g₁ [] g₂ >′)∘ f  ≡⟨ commute₂ ○ - ⟩
                  g₂    ∘ f  ∎)

  eta : {□ : a ∘ p ≡ b ∘ q} → < p [ □ ] q >′ ≡ id
  eta = sym $ unique (∘-idʳ 𝓒) (∘-idʳ 𝓒)

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
      { ⊗₍₎   = λ A B  a   b  → apex    (pull a b)
      ; p     = λ {a = a} {b} → p       (pull a b)
      ; q     = λ {a = a} {b} → q       (pull a b)
      ; <[-]> = λ {a = a} {b} → mediate (pull a b)
      } where open Pullback
