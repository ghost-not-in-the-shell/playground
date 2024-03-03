module Prelude.Nat where
open import Prelude.Bool

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

private
  _=='_ : Nat → Nat → Bool
  zero  ==' zero  = true
  zero  ==' suc _ = false
  suc m ==' zero  = false
  suc m ==' suc n = m ==' n

instance
  Nat-eq : Eq Nat
  Nat-eq = record { _==_ = _=='_ }

infix 4 _<_
_<_ : Nat → Nat → Bool
_     < zero  = false
zero  < suc _ = true
suc m < suc n = m < n

plus : Nat → Nat → Nat
plus zero    n = n
plus (suc m) n = suc (plus m n)
