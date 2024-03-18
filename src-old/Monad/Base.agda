{-# OPTIONS --type-in-type #-}
module Monad.Base where
open import Prelude
open import Category.Base
open import Functor.Base
open import NaturalTransformation.Base

record MonadicOp {𝓒 : Category} (𝓜 : 𝓒 ⟶ 𝓒) : Set where
  field
    return : ∀ {A} → 𝓒 ∣ A ⟶ 𝓜 ₀(A)
    join   : ∀ {A} → 𝓒 ∣ 𝓜 ₀(𝓜 ₀(A)) ⟶ 𝓜 ₀(A)

  infixl 4 _=<<_
  _=<<_ : ∀ {A B}
    → 𝓒 ∣      A  ⟶ 𝓜 ₀(B)
    → 𝓒 ∣ 𝓜 ₀(A) ⟶ 𝓜 ₀(B)
  _=<<_ = λ f → join ∘ 𝓜 ₁(f)

  infixl 4 _>=>_
  _>=>_ : ∀ {A B C}
    → 𝓒 ∣ A ⟶ 𝓜 ₀(B)
    → 𝓒 ∣ B ⟶ 𝓜 ₀(C)
    → 𝓒 ∣ A ⟶ 𝓜 ₀(C)
  f >=> g = join ∘ 𝓜 ₁(g) ∘ f

  infixr 4 _<=<_
  _<=<_ : ∀ {A B C}
    → 𝓒 ∣ B ⟶ 𝓜 ₀(C)
    → 𝓒 ∣ A ⟶ 𝓜 ₀(B)
    → 𝓒 ∣ A ⟶ 𝓜 ₀(C)
  _<=<_ = flip _>=>_

open MonadicOp ⦃...⦄ public

{-# DISPLAY MonadicOp.return _ = return #-}
{-# DISPLAY MonadicOp.join   _ = join   #-}
{-# DISPLAY MonadicOp._>=>_  _ = _>=>_  #-}
{-# DISPLAY MonadicOp._<=<_  _ = _<=<_  #-}

record Monad {𝓒 : Category} (𝓜 : 𝓒 ⟶ 𝓒) : Set where
  field
    unit : id ⟹ 𝓜
    -- natural unit : ∀ {A B} {f : 𝓒 ∣ A ⟶ B} → return ∘ f ≡ 𝓜 ₁(f) ∘ return
    mult : 𝓜 ∘ 𝓜 ⟹ 𝓜
    -- natural mult : ∀ {A B} {f : 𝓒 ∣ A ⟶ B} → join ∘ 𝓜 ₁(𝓜 ₁(f)) ≡ 𝓜 ₁(f) ∘ join

    identityˡ : ∀ {A} → mult ₍ A ₎ ∘ 𝓜 ₁(unit ₍ A ₎) ≡ id
    identityʳ : ∀ {A} → mult ₍ A ₎ ∘ unit ₍ 𝓜 ₀(A) ₎ ≡ id
    assoc : ∀ {A} → mult ⋆ ∘ 𝓜 ₁(mult ₍ A ₎) ≡ mult ⋆ ∘ mult ₍ 𝓜 ₀(A) ₎

  monadic : MonadicOp 𝓜
  monadic = record
    { return = unit ⋆
    ; join   = mult ⋆
    }

open Monad public
