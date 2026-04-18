module Prelude.Idiom.Underlying where
open import Prelude.Prim

record Underlying (A : Type) : Type where
  constructor underlying-instance
  field
    ⌞_⌟ : A → Type

open Underlying ⦃...⦄ using (⌞_⌟) public

record Funlike (Fun : Type) (Arg : Type) (Out : Arg → Type) : Type where
  constructor funlike-instance
  infix 6 _₍_₎ _▴
  field
    _₍_₎ : (f : Fun) (x : Arg) → Out x

  _▴ : (f : Fun) {x : Arg} → Out x
  f ▴ = f ₍ _ ₎

open Funlike ⦃...⦄ public

{-# DISPLAY Funlike._₍_₎ _ = _₍_₎ #-}
{-# DISPLAY Funlike._▴   _ = _▴   #-}
