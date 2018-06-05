module Jellyfish.SuperCombinator.Syntax.WithToplevels where
open import Jellyfish.Prelude

infix 4 _[_]⊢_
data _[_]⊢_ (Ε : List Sig) (Γ : Con) : Ty → Set where
  lit : Nat
      ------------
      → Ε [ Γ ]⊢ ℕ

  add : Ε [ Γ ]⊢ ℕ
      → Ε [ Γ ]⊢ ℕ
      ------------
      → Ε [ Γ ]⊢ ℕ

  sub : Ε [ Γ ]⊢ ℕ
      → Ε [ Γ ]⊢ ℕ
      ------------
      → Ε [ Γ ]⊢ ℕ

  mul : Ε [ Γ ]⊢ ℕ
      → Ε [ Γ ]⊢ ℕ
      ------------
      → Ε [ Γ ]⊢ ℕ

  ifz : ∀ {A}
    → Ε [ Γ ]⊢ ℕ
    → Ε [ Γ ]⊢ A
    → Ε [ Γ ]⊢ A
    ------------
    → Ε [ Γ ]⊢ A

  var : ∀ {A}
    →     Γ  ∋ A
    ------------
    → Ε [ Γ ]⊢ A

  cls : ∀ {A⃗ A B}
    → Ε      ∋ (A⃗ ▻ A) , B
    →     Γ  ∋⃗ A⃗
    ----------------------
    → Ε [ Γ ]⊢ A ⇒ B

  app : ∀ {A B}
    → Ε [ Γ ]⊢ A ⇒ B
    → Ε [ Γ ]⊢ A
    ----------------
    → Ε [ Γ ]⊢ B

  lεt : ∀ {A B}
    → Ε [ Γ     ]⊢ A
    → Ε [ Γ ▻ A ]⊢ B
    ----------------
    → Ε [ Γ     ]⊢ B

Defs : List Sig → Set
Defs Ε = All (λ { (Γ , A) → Ε [ Γ ]⊢ A }) Ε

Prog : List Sig → Ty → Set
Prog Ε A = Defs Ε × Ε [ ε ]⊢ A

▻▻-wk∋ : ∀ {Ε₁ A} (Ε₂ : List Sig) → Ε₁ ∋ A → (Ε₁ ▻▻ Ε₂) ∋ A
▻▻-wk∋ ε        ze     = ze
▻▻-wk∋ (Ε₂ ▻ _) ze     = su (▻▻-wk∋ Ε₂ ze)
▻▻-wk∋ ε        (su x) = su x
▻▻-wk∋ (Ε₂ ▻ _) (su x) = su (▻▻-wk∋ Ε₂ (su x))

▻▻-wk⊢ : ∀ {Ε₁ Γ A} Ε₂ → Ε₁ [ Γ ]⊢ A → Ε₁ ▻▻ Ε₂ [ Γ ]⊢ A
▻▻-wk⊢ Ε₂ (lit n) = lit n
▻▻-wk⊢ Ε₂ (add e₁ e₂) = add (▻▻-wk⊢ Ε₂ e₁) (▻▻-wk⊢ Ε₂ e₂)
▻▻-wk⊢ Ε₂ (sub e₁ e₂) = sub (▻▻-wk⊢ Ε₂ e₁) (▻▻-wk⊢ Ε₂ e₂)
▻▻-wk⊢ Ε₂ (mul e₁ e₂) = mul (▻▻-wk⊢ Ε₂ e₁) (▻▻-wk⊢ Ε₂ e₂)
▻▻-wk⊢ Ε₂ (ifz e₁ e₂ e₃) = ifz (▻▻-wk⊢ Ε₂ e₁) (▻▻-wk⊢ Ε₂ e₂) (▻▻-wk⊢ Ε₂ e₃)
▻▻-wk⊢ Ε₂ (var x) = var x
▻▻-wk⊢ Ε₂ (cls f x⃗) = cls (▻▻-wk∋ Ε₂ f) x⃗
▻▻-wk⊢ Ε₂ (app e₁ e₂) = app (▻▻-wk⊢ Ε₂ e₁) (▻▻-wk⊢ Ε₂ e₂)
▻▻-wk⊢ Ε₂ (lεt e₁ e₂) = lεt (▻▻-wk⊢ Ε₂ e₁) (▻▻-wk⊢ Ε₂ e₂)
