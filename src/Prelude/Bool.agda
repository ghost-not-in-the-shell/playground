module Prelude.Bool where

data Bool : Set where
  false : Bool
  true  : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN FALSE false #-}
{-# BUILTIN TRUE  true  #-}

infix 0 if_then_else_
if_then_else_ : ∀ {P : Bool → Set} (b : Bool) → P true → P false → P b
if true  then t else f = t
if false then t else f = f

record Eq (A : Set) : Set where
  infix 4 _==_
  field
    _==_ : A → A → Bool

open Eq ⦃ ... ⦄ public
