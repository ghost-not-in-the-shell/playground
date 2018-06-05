module Jellyfish.Prelude where
open import Agda.Primitive                public
open import Jellyfish.Prelude.Bool        public
open import Jellyfish.Prelude.Char        public
open import Jellyfish.Prelude.Dec         public
open import Jellyfish.Prelude.Equality    public
open import Jellyfish.Prelude.Empty       public
open import Jellyfish.Prelude.Fin         public
open import Jellyfish.Prelude.Function    public
open import Jellyfish.Prelude.List        public
open import Jellyfish.Prelude.Maybe       public
open import Jellyfish.Prelude.Monad       public
open import Jellyfish.Prelude.Nat         public
open import Jellyfish.Prelude.Product     public
open import Jellyfish.Prelude.Subset      public
open import Jellyfish.Prelude.String      public
open import Jellyfish.Prelude.Sum         public

-------------------------------------------------------------------------------
-- Type

infixr 6 _⇒_
data Ty : Set where
  ℕ   : Ty
  _⇒_ : Ty → Ty → Ty

⇒-injectiveˡ : ∀ {A₁ A₂ B₁ B₂} → A₁ ⇒ B₁ ≡ A₂ ⇒ B₂ → A₁ ≡ A₂
⇒-injectiveˡ refl = refl

⇒-injectiveʳ : ∀ {A₁ A₂ B₁ B₂} → A₁ ⇒ B₁ ≡ A₂ ⇒ B₂ → B₁ ≡ B₂
⇒-injectiveʳ refl = refl

instance
  Ty-dec-eq : Eq Ty
  _≟_ ⦃ Ty-dec-eq ⦄ ℕ         ℕ         = yes refl
  _≟_ ⦃ Ty-dec-eq ⦄ ℕ         (A₂ ⇒ B₂) = no λ ()
  _≟_ ⦃ Ty-dec-eq ⦄ (A₁ ⇒ B₁) ℕ         = no λ ()
  _≟_ ⦃ Ty-dec-eq ⦄ (A₁ ⇒ B₁) (A₂ ⇒ B₂) with A₁ ≟ A₂ | B₁ ≟ B₂
  ... | yes p | yes q = yes (_⇒_ ⟨$⟩ p ⟨*⟩ q)
  ... | yes p | no ¬q = no λ r → ⇒-injectiveʳ r ↯ ¬q
  ... | no ¬p | _     = no λ r → ⇒-injectiveˡ r ↯ ¬p

-------------------------------------------------------------------------------
-- Context

Con : Set
Con = List Ty

EnvDesc : Set
EnvDesc = Con

-------------------------------------------------------------------------------
-- Signature of top-level functions

Sig : Set
Sig = List Ty × Ty

-------------------------------------------------------------------------------
-- Renaming

infix 4 _∋⃗_
_∋⃗_ : Con → Con → Set
Γ ∋⃗ A⃗ = All (Γ ∋_) A⃗

id∋⃗ : ∀ {Γ} → Γ ∋⃗ Γ
id∋⃗ {ε}     = ε
id∋⃗ {Γ ▻ A} = map su id∋⃗ ▻ ze

-------------------------------------------------------------------------------
-- Stack

StackDesc : Set
StackDesc = List Ty
