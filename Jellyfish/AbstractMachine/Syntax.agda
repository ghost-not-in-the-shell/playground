module Jellyfish.AbstractMachine.Syntax where
open import Jellyfish.Prelude hiding (_▻▻_; _▻▻▻_)

record StateDesc : Set where
  constructor [_,_]
  field
    env-desc   : EnvDesc
    stack-desc : StackDesc

mutual
  data Code : StateDesc → StateDesc → Set where
    lit : ∀ {Γ Σ} → Nat → Code [ Γ , Σ ] [ Γ , Σ ▻ ℕ ]
    add : ∀ {Γ Σ}       → Code [ Γ , Σ ▻ ℕ ▻ ℕ ] [ Γ , Σ ▻ ℕ ]
    sub : ∀ {Γ Σ}       → Code [ Γ , Σ ▻ ℕ ▻ ℕ ] [ Γ , Σ ▻ ℕ ]
    mul : ∀ {Γ Σ}       → Code [ Γ , Σ ▻ ℕ ▻ ℕ ] [ Γ , Σ ▻ ℕ ]
    ifz : ∀ {Γ Σ A}
      → Code⋆ [ Γ , Σ     ] [ Γ , Σ ▻ A ]
      → Code⋆ [ Γ , Σ     ] [ Γ , Σ ▻ A ]
      → Code  [ Γ , Σ ▻ ℕ ] [ Γ , Σ ▻ A ]
    var  : ∀ {Γ Σ A} → Γ ∋ A → Code [ Γ     , Σ     ] [ Γ     , Σ ▻ A ]
    push : ∀ {Γ Σ A}         → Code [ Γ     , Σ ▻ A ] [ Γ ▻ A , Σ     ]
    pop  : ∀ {Γ Σ A}         → Code [ Γ ▻ A , Σ     ] [ Γ     , Σ     ]
    lam  : ∀ {Γ Σ A B}
      → (∀ {Σ′} → Code⋆ [ Γ ▻ A , Σ′ ] [ Γ ▻ A , Σ′ ▻ B ])
      → Code  [ Γ , Σ ] [ Γ , Σ ▻ A ⇒ B ]
    app : ∀ {Γ Σ A B}
      → Code [ Γ , Σ ▻ A ⇒ B ▻ A ] [ Γ , Σ ▻ B ]

  data Code⋆ : StateDesc → StateDesc → Set where
    ε   : ∀ {d} → Code⋆ d d
    _▻_ : ∀ {d₁ d₂ d₃} → Code⋆ d₁ d₂ → Code d₂ d₃ → Code⋆ d₁ d₃

infixr 5 _▻▻_
_▻▻_ : ∀ {d₁ d₂ d₃} → Code⋆ d₁ d₂ → Code⋆ d₂ d₃ → Code⋆ d₁ d₃
c₁ ▻▻ ε = c₁
c₁ ▻▻ (c₂ ▻ c) = (c₁ ▻▻ c₂) ▻ c
