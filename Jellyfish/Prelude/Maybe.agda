module Jellyfish.Prelude.Maybe where

data Maybe {𝔞} (A : Set 𝔞) : Set 𝔞 where
  nothing :     Maybe A
  just    : A → Maybe A

open import Jellyfish.Prelude.Monad

instance
  Maybe-functor : ∀ {𝔞} → Functor λ (A : Set 𝔞) → Maybe A
  _<$>_ ⦃ Maybe-functor ⦄ f (just x)  = just (f x)
  _<$>_ ⦃ Maybe-functor ⦄ f (nothing) = nothing

  Maybe-applicative : ∀ {𝔞} → Applicative λ (A : Set 𝔞) → Maybe A
  pure ⦃ Maybe-applicative ⦄ = just

  _<*>_ ⦃ Maybe-applicative ⦄ (just f) (just x) = just (f x)
  _<*>_ ⦃ Maybe-applicative ⦄ _        _        = nothing

  Maybe-monad : ∀ {𝔞} → Monad λ (A : Set 𝔞) → Maybe A
  _>>=_ ⦃ Maybe-monad ⦄ (just x)  f = f x
  _>>=_ ⦃ Maybe-monad ⦄ (nothing) f = nothing

  Maybe-functor-zero : ∀ {𝔞} → FunctorZero λ (A : Set 𝔞) → Maybe A
  empty ⦃ Maybe-functor-zero ⦄ = nothing

  Maybe-alternative : ∀ {𝔞} → Alternative λ (A : Set 𝔞) → Maybe A
  _<|>_ ⦃ Maybe-alternative ⦄ nothing y = y
  _<|>_ ⦃ Maybe-alternative ⦄ x       y = x
