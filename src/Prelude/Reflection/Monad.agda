module Prelude.Reflection.Monad where
open import Prelude.Prim
open import Prelude.Reflection.Argument
open import Prelude.Reflection.Error
open import Prelude.Reflection.Meta
open import Prelude.Reflection.Name
open import Prelude.Reflection.Term

postulate
  TC : ∀ {ℓ₁ ℓ₂} → Type ℓ₁ → Type ℓ₂

  return : ∀ {ℓ} {A : Type ℓ} → A → TC A
  bind   : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → TC A → (A → TC B) → TC B
  error  : ∀ {ℓ} {A : Type ℓ} → List Error → TC A
  catch  : ∀ {ℓ} {A : Type ℓ} → TC A → TC A → TC A

  quote-term   : ∀ {ℓ} {A : Type ℓ} → A → TC Term
  unquote-term : ∀ {ℓ} {A : Type ℓ} → Term → TC A

  infer     : Term → TC Term
  check     : Term → Term → TC Term
  reduce    : Term → TC Term
  normalise : Term → TC Term
  unify     : Term → Term → TC ⊤
  block     : ∀ {ℓ} {A : Type ℓ} → Blocker → TC A

  with-normalisation : ∀ {ℓ} {A : Type ℓ} → Bool → TC A → TC A
  with-reconstructed : ∀ {ℓ} {A : Type ℓ} → Bool → TC A → TC A
  with-expand-last   : ∀ {ℓ} {A : Type ℓ} → Bool → TC A → TC A
  with-reduce-defs   : ∀ {ℓ} {A : Type ℓ} → Σ Bool (λ _ → List Name) → TC A → TC A
  no-constraints     : ∀ {ℓ} {A : Type ℓ} → TC A → TC A

  debug-print : String → Nat → List Error → TC ⊤

{-# BUILTIN AGDATCM            TC           #-}
{-# BUILTIN AGDATCMRETURN      return       #-}
{-# BUILTIN AGDATCMBIND        bind         #-}
{-# BUILTIN AGDATCMTYPEERROR   error        #-}
{-# BUILTIN AGDATCMCATCHERROR  catch        #-}
{-# BUILTIN AGDATCMQUOTETERM   quote-term   #-}
{-# BUILTIN AGDATCMUNQUOTETERM unquote-term #-}
{-# BUILTIN AGDATCMINFERTYPE   infer        #-}
{-# BUILTIN AGDATCMCHECKTYPE   check        #-}
{-# BUILTIN AGDATCMNORMALISE   normalise    #-}
{-# BUILTIN AGDATCMREDUCE      reduce       #-}
{-# BUILTIN AGDATCMUNIFY       unify        #-}
{-# BUILTIN AGDATCMBLOCK       block        #-}
{-# BUILTIN AGDATCMWITHNORMALISATION with-normalisation #-}
{-# BUILTIN AGDATCMWITHRECONSTRUCTED with-reconstructed #-}
{-# BUILTIN AGDATCMWITHEXPANDLAST    with-expand-last   #-}
{-# BUILTIN AGDATCMWITHREDUCEDEFS    with-reduce-defs   #-}
{-# BUILTIN AGDATCMNOCONSTRAINTS     no-constraints     #-}
{-# BUILTIN AGDATCMDEBUGPRINT        debug-print        #-}

infixl 1 _>>=_
_>>=_ = bind

infixl 3 _<|>_
_<|>_ = catch
