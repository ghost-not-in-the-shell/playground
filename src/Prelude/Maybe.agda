module Prelude.Maybe where
open import Prelude.Function
open import Prelude.Idiom

data Maybe (A : Set) : Set where
  nothing :     Maybe A
  just    : A → Maybe A

{-# BUILTIN MAYBE Maybe #-}

private
  variable
    A B : Set

  map' : (A → B) → Maybe A → Maybe B
  map' f nothing = nothing
  map' f (just x) = just (f x)

  _<*>'_ : Maybe (A → B) → Maybe A → Maybe B
  just f  <*>' just x = just $ f x
  _ <*>' _ = nothing

  bind : Maybe A → (A → Maybe B) → Maybe B
  bind nothing _ = nothing
  bind (just x) f = f x

instance
  Maybe-map : Map Maybe
  Maybe-map = record { map = map' }

  Maybe-applicative : Applicative Maybe
  Maybe-applicative = record { pure = just; _<*>_ = _<*>'_ }

  Maybe-bind : Bind Maybe
  Maybe-bind = record { return = just; _>>=_ = bind }
