module Prelude.Reflection.Literal where
open import Prelude.Char
open import Prelude.Float
open import Prelude.Nat
open import Prelude.String
open import Prelude.Word
open import Prelude.Reflection.Meta
open import Prelude.Reflection.Name

data Literal : Set where
  nat    : Nat    → Literal
  float  : Float  → Literal
  char   : Char   → Literal  
  string : String → Literal
  word   : Word   → Literal
  meta   : Meta   → Literal
  name   : Name   → Literal  

{-# BUILTIN AGDALITERAL   Literal #-}
{-# BUILTIN AGDALITNAT    nat     #-}
{-# BUILTIN AGDALITFLOAT  float   #-}
{-# BUILTIN AGDALITCHAR   char    #-}
{-# BUILTIN AGDALITSTRING string  #-}
{-# BUILTIN AGDALITWORD64 word    #-}
{-# BUILTIN AGDALITQNAME  name    #-}
{-# BUILTIN AGDALITMETA   meta    #-}
