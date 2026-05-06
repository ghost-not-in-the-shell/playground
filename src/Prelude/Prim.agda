module Prelude.Prim where

open import Agda.Primitive public
  using    ( SSet )
  renaming ( Set to Type )
open import Agda.Primitive.Cubical public
  renaming ( I          to 𝕀
           ; primIMin   to _∧_
           ; primIMax   to _∨_
           ; primINeg   to ~_
           ; primComp   to comp
           ; primHComp  to hcomp
           ; primTransp to transp )
open import Agda.Builtin.Cubical.Path public
open import Agda.Builtin.Cubical.Sub public
  renaming ( primSubOut to outS )

open import Agda.Builtin.Bool   public
open import Agda.Builtin.Char   public
open import Agda.Builtin.Float  public
open import Agda.Builtin.List   public
open import Agda.Builtin.Maybe  public
open import Agda.Builtin.Nat    public
open import Agda.Builtin.Sigma  public
open import Agda.Builtin.String public
open import Agda.Builtin.Unit   public
open import Agda.Builtin.Word   public

private module Formula where
  𝔽 = 𝕀

open Formula public

private module Partial where
  infix 4 _[_↦_]
  _[_↦_] : ∀ {ℓ} (A : Type ℓ) (φ : 𝔽) (u : Partial φ A) → SSet ℓ
  _[_↦_] = Sub

open Partial public

private module Path where
  Path : ∀ {ℓ} (A : Type ℓ) (a₀ a₁ : A) → Type ℓ
  Path A = PathP (λ i → A)

  infix 4 PathP-syntax
  PathP-syntax = PathP
  syntax PathP-syntax (λ i → A) a₀ a₁ = a₀ ≡ a₁ [ i ↦ A ]

open Path public

private module Misc where
  infix 4 -,
  pattern -, b = _ , b

  infix 2 Σ-syntax
  Σ-syntax = Σ
  syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

  const : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂}
    → (x : A) → B x → A
  const x = λ _ → x

  flip : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : A → B → Type ℓ₃}
    → (∀ x y → C x y) → (∀ y x → C x y)
  flip f = λ y x → f x y

  infixr -1 _$_
  _$_ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂}
    → (∀ x → B x) → (∀ x → B x)
  f $ x = f x

open Misc public

postulate
  🚧 : ∀ {ℓ} {A : Type ℓ} → A
