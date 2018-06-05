module Jellyfish.AbstractMachine.Semantics where
open import Jellyfish.Prelude hiding (_▻▻_; _▻▻▻_)
open import Jellyfish.AbstractMachine.Syntax

mutual
  {-# TERMINATING #-}
  ⟦_⟧ : Ty → Set
  ⟦ ℕ     ⟧ = Nat
  ⟦ A ⇒ B ⟧ = ∃ λ Γ → Env Γ × ∀ {Σ′} → Code⋆ [ Γ ▻ A , Σ′ ] [ Γ ▻ A , Σ′ ▻ B ]

  Env : EnvDesc → Set
  Env = All ⟦_⟧

  Stack : StackDesc → Set
  Stack = All ⟦_⟧

record State (desc : StateDesc) : Set where
  constructor [_,_]
  open StateDesc desc
  field
    env   : Env   env-desc
    stack : Stack stack-desc

mutual
  {-# TERMINATING #-}
  step : ∀ {Γ₁ Σ₁ Γ₂ Σ₂} → Code [ Γ₁ , Σ₁ ] [ Γ₂ , Σ₂ ] → State [ Γ₁ , Σ₁ ] → State [ Γ₂ , Σ₂ ]
  step (lit n) [ ρ , σ           ] = [ ρ , σ ▻ n       ]
  step add     [ ρ , σ ▻ n₁ ▻ n₂ ] = [ ρ , σ ▻ n₁ + n₂ ]
  step sub     [ ρ , σ ▻ n₁ ▻ n₂ ] = [ ρ , σ ▻ n₁ - n₂ ]
  step mul     [ ρ , σ ▻ n₁ ▻ n₂ ] = [ ρ , σ ▻ n₁ * n₂ ]
  step (ifz c₂ c₃) [ ρ , σ ▻ zero  ] = step⋆ c₂ [ ρ , σ ]
  step (ifz c₂ c₃) [ ρ , σ ▻ suc n ] = step⋆ c₃ [ ρ , σ ]
  step (var x) [ ρ , σ ] = [ ρ , σ ▻ find ρ x ]
  step push [ ρ     , σ ▻ a ] = [ ρ ▻ a , σ ]
  step pop  [ ρ ▻ a , σ     ] = [ ρ     , σ ]
  step (lam c) [ ρ , σ ] = [ ρ , σ ▻ (_ , ρ , λ {Σ′} → c {Σ′}) ]
  step app [ ρ , σ ▻ (_ , ρ′ , c) ▻ a ] with step⋆ c [ ρ′ ▻ a , ε ]
  ... | [ _ , ε ▻ b ] = [ ρ , σ ▻ b ]

  step⋆ : ∀ {Γ₁ Σ₁ Γ₂ Σ₂} → Code⋆ [ Γ₁ , Σ₁ ] [ Γ₂ , Σ₂ ] → State [ Γ₁ , Σ₁ ] → State [ Γ₂ , Σ₂ ]
  step⋆ ε        [ ρ , σ ] = [ ρ , σ ]
  step⋆ (c⋆ ▻ c) [ ρ , σ ] = step c (step⋆ c⋆ [ ρ , σ ])

mutual
  data Step : ∀ {Γ₁ Σ₁ Γ₂ Σ₂} → Code [ Γ₁ , Σ₁ ] [ Γ₂ , Σ₂ ] → State [ Γ₁ , Σ₁ ] → State [ Γ₂ , Σ₂ ] → Set where
    lit : ∀ {Γ Σ} {ρ : Env Γ} {σ : Stack Σ} (n : Nat)
      → Step (lit n) [ ρ , σ ] [ ρ , σ ▻ n ]

    add : ∀ {Γ Σ} {ρ : Env Γ} {σ : Stack Σ} {n₁ n₂ : Nat}
      → Step add [ ρ , σ ▻ n₁ ▻ n₂ ] [ ρ , σ ▻ n₁ + n₂ ]

    sub : ∀ {Γ Σ} {ρ : Env Γ} {σ : Stack Σ} {n₁ n₂ : Nat}
      → Step sub [ ρ , σ ▻ n₁ ▻ n₂ ] [ ρ , σ ▻ n₁ - n₂ ]

    mul : ∀ {Γ Σ} {ρ : Env Γ} {σ : Stack Σ} {n₁ n₂ : Nat}
      → Step mul [ ρ , σ ▻ n₁ ▻ n₂ ] [ ρ , σ ▻ n₁ * n₂ ]

    ifz/t : ∀ {Γ Σ A} {ρ : Env Γ} {σ : Stack Σ} {a : ⟦ A ⟧}
              {c₂ : Code⋆ [ Γ , Σ ] [ Γ , Σ ▻ A ]}
              {c₃ : Code⋆ [ Γ , Σ ] [ Γ , Σ ▻ A ]}
      → Step⋆ c₂ [ ρ , σ ] [ ρ , σ ▻ a ]
      → Step (ifz c₂ c₃) [ ρ , σ ▻ zero ] [ ρ , σ ▻ a ]

    ifz/f : ∀ {Γ Σ A} {ρ : Env Γ} {σ : Stack Σ} {n} {a : ⟦ A ⟧}
              {c₂ : Code⋆ [ Γ , Σ ] [ Γ , Σ ▻ A ]}
              {c₃ : Code⋆ [ Γ , Σ ] [ Γ , Σ ▻ A ]}
      → Step⋆ c₃ [ ρ , σ ] [ ρ , σ ▻ a ]
      → Step (ifz c₂ c₃) [ ρ , σ ▻ suc n ] [ ρ , σ ▻ a ]

    var : ∀ {Γ Σ A} {ρ : Env Γ} {σ : Stack Σ} (x : Γ ∋ A)
      → Step (var x) [ ρ , σ ] [ ρ , σ ▻ find ρ x ]

    push : ∀ {Γ Σ A} {ρ : Env Γ} {σ : Stack Σ} {a : ⟦ A ⟧}
      → Step push [ ρ , σ ▻ a ] [ ρ ▻ a , σ ]

    pop : ∀ {Γ Σ A} {ρ : Env Γ} {σ : Stack Σ} {a : ⟦ A ⟧}
      → Step pop [ ρ ▻ a , σ ] [ ρ , σ ]

    lam : ∀ {Γ Σ A B} {ρ : Env Γ} {σ : Stack Σ}
            {c : ∀ {Σ′} → Code⋆ [ Γ ▻ A , Σ′ ] [ Γ ▻ A , Σ′ ▻ B ]}
      → Step (lam c) [ ρ , σ ] [ ρ , σ ▻ (Γ , ρ , λ {Σ′} → c {Σ′}) ]

    app : ∀ {Γ Γ′ Σ A B} {ρ : Env Γ} {ρ′ : Env Γ′} {σ : Stack Σ} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
            {c : ∀ {Σ′} → Code⋆ [ Γ′ ▻ A , Σ′ ] [ Γ′ ▻ A , Σ′ ▻ B ]}
      → Step⋆ c  [ ρ′ ▻ a , σ                                  ] [ ρ′ ▻ a , σ ▻ b ]
      → Step app [ ρ      , σ ▻ (_ , ρ′ , λ {Σ′} → c {Σ′}) ▻ a ] [ ρ      , σ ▻ b ]

  data Step⋆ : ∀ {Γ₁ Σ₁ Γ₂ Σ₂} → Code⋆ [ Γ₁ , Σ₁ ] [ Γ₂ , Σ₂ ] → State [ Γ₁ , Σ₁ ] → State [ Γ₂ , Σ₂ ] → Set where
    ε   : ∀ {Γ Σ} {ρ : Env Γ} {σ : Stack Σ} → Step⋆ ε [ ρ , σ ] [ ρ , σ ]
    _▻_ : ∀ {Γ₁ Σ₁ Γ₂ Σ₂ Γ₃ Σ₃}
            {ρ₁ : Env   Γ₁} {ρ₂ : Env   Γ₂} {ρ₃ : Env   Γ₃}
            {σ₁ : Stack Σ₁} {σ₂ : Stack Σ₂} {σ₃ : Stack Σ₃}
            {c⋆ : Code⋆ [ Γ₁ , Σ₁ ] [ Γ₂ , Σ₂ ]}
            {c  : Code  [ Γ₂ , Σ₂ ] [ Γ₃ , Σ₃ ]}
      → Step⋆ c⋆ [ ρ₁ , σ₁ ] [ ρ₂ , σ₂ ]
      → Step  c  [ ρ₂ , σ₂ ] [ ρ₃ , σ₃ ]
      → Step⋆ (c⋆ ▻ c) [ ρ₁ , σ₁ ] [ ρ₃ , σ₃ ]

_▻▻▻_ : ∀ {Γ₁ Σ₁ Γ₂ Σ₂ Γ₃ Σ₃}
          {ρ₁ : Env   Γ₁} {ρ₂ : Env   Γ₂} {ρ₃ : Env   Γ₃}
          {σ₁ : Stack Σ₁} {σ₂ : Stack Σ₂} {σ₃ : Stack Σ₃}
          {c₁ : Code⋆ [ Γ₁ , Σ₁ ] [ Γ₂ , Σ₂ ]}
          {c₂ : Code⋆ [ Γ₂ , Σ₂ ] [ Γ₃ , Σ₃ ]}
        → Step⋆ c₁ [ ρ₁ , σ₁ ] [ ρ₂ , σ₂ ]
        → Step⋆ c₂ [ ρ₂ , σ₂ ] [ ρ₃ , σ₃ ]
        → Step⋆ (c₁ ▻▻ c₂) [ ρ₁ , σ₁ ] [ ρ₃ , σ₃ ]
d₁ ▻▻▻ ε        = d₁
d₁ ▻▻▻ (d₂ ▻ d) = (d₁ ▻▻▻ d₂) ▻ d
