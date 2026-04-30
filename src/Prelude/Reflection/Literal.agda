module Prelude.Reflection.Literal where
open import Prelude.Prim
open import Prelude.Reflection.Meta
open import Prelude.Reflection.Name

data Literal : Type where
  nat    : Nat    → Literal
  float  : Float  → Literal
  char   : Char   → Literal
  string : String → Literal
  word   : Word   → Literal
  name   : Name   → Literal
  meta   : Meta   → Literal

{-# BUILTIN AGDALITERAL   Literal #-}
{-# BUILTIN AGDALITNAT    nat     #-}
{-# BUILTIN AGDALITFLOAT  float   #-}
{-# BUILTIN AGDALITCHAR   char    #-}
{-# BUILTIN AGDALITSTRING string  #-}
{-# BUILTIN AGDALITWORD64 word    #-}
{-# BUILTIN AGDALITQNAME  name    #-}
{-# BUILTIN AGDALITMETA   meta    #-}

