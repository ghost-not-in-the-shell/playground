open import Category.Monad
open import Data.List
open import Data.List.Any
open import Data.List.Membership.Propositional
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function hiding (_∋_)

open RawMonad ⦃...⦄

instance
  Maybe-monad = monad

pattern ze   = here  refl
pattern su α = there α

data Ty : Set where
  𝟙 : Ty
  𝔸 : Ty

Sig = List Ty

infix 4 _∋_
_∋_ : ∀ {A} → List A → A → Set
xs ∋ x = x ∈ xs

infix 4 _⊢_
data _⊢_ (Σ : Sig) : Ty → Set where
  meta : ∀ {τ}
    → Σ ∋ τ
    → Σ ⊢ τ

  sole : Σ ⊢ 𝟙

  ε   : Σ ⊢ 𝔸
  _∙_ : Σ ⊢ 𝔸 → Σ ⊢ 𝔸 → Σ ⊢ 𝔸

_-_ : ∀ {τ} Σ → τ ∈ Σ → Sig
[] - ()
(τ ∷ Σ) - ze     = Σ
(σ ∷ Σ) - (su α) = σ ∷ Σ - α

thin : ∀ {Σ σ τ} (α : σ ∈ Σ)
  → τ ∈ Σ - α
  → τ ∈ Σ
thin ze     β      = su β
thin (su α) ze     = ze
thin (su α) (su β) = su (thin α β)

thick : ∀ {Σ σ τ} (α : σ ∈ Σ)
  →        Σ     ∋ τ
  → Maybe (Σ - α ∋ τ)
thick ze ze = nothing
thick ze (su β) = just β
thick (su α) ze = just ze
thick (su α) (su β) = su <$> thick α β

check : ∀ {Σ τ}
  → (α : Σ ∋ τ)
  →      Σ ⊢ τ
  → Maybe (Σ - α ⊢ τ)
check α (meta β) = meta <$> thick α β -- this would never be called
check α sole     = just sole
check α ε        = just ε
check α (t ∙ u)  = _∙_ <$> check α t ⊛ check α u

infix 4 _≼_
data _≼_ : Sig → Sig → Set where
  done  : ∀ {Σ} → Σ ≼ Σ
  _≔_∷_ : ∀ {Σ Σ′ τ}
    → (x : τ ∈ Σ′)
    → Σ′ - x ⊢ τ
    → Σ ≼ Σ′ - x
    → Σ ≼ Σ′

flex-flex : ∀ {Σ τ}
  → Σ ∋ τ
  → Σ ∋ τ
  → ∃ (_≼ Σ)
flex-flex α β with thick α β
... | nothing = _ , done
... | just β′ = _ , α ≔ meta β′ ∷ done

unify : ∀ {Σ τ} → Σ ⊢ τ → Σ ⊢ τ → ∃ (_≼ Σ) → Maybe (∃ (_≼ Σ))
unify sole sole ρ = just ρ
unify ε ε ρ = just ρ
unify ε (_ ∙ _) ρ = nothing
unify (_ ∙ _) ε ρ = nothing
unify (t₁ ∙ u₁) (t₂ ∙ u₂) ρ = unify t₁ t₂ ρ >>= unify u₁ u₂
unify (meta α) (meta β) (_ , done) = return (flex-flex α β)
unify (meta α) t        (_ , done) = check α t >>= λ t′ → return (_ , (α ≔ t′ ∷ done))
unify t        (meta α) (_ , done) = check α t >>= λ t′ → return (_ , (α ≔ t′ ∷ done))
unify t₁       t₂       (_ , α ≔ t ∷ ρ) =
  unify {!!} {!!} (_ , ρ) >>= λ { (_ , ρ′) → return (_ , α ≔ t ∷ ρ′) }

solve : ∀ {Σ} → ∃ (All (Σ ⊢_ , Σ ⊢_))
