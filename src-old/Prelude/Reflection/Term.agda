module Prelude.Reflection.Term where
open import Prelude.List
open import Prelude.Nat
open import Prelude.Sigma
open import Prelude.String
open import Prelude.Reflection.Argument
open import Prelude.Reflection.Literal
open import Prelude.Reflection.Meta
open import Prelude.Reflection.Name

data Abs (A : Set) : Set where
  abs : String → A → Abs A

{-# BUILTIN ABS Abs    #-}
{-# BUILTIN ABSABS abs #-}

data Term    : Set
data Sort    : Set
data Pattern : Set
data Clause  : Set

data Term where
  sort    : Sort                          → Term
  lit     : Literal                       → Term
  con     : Name → List (Arg Term)        → Term
  pi      : Arg Term → Abs Term           → Term    
  lam     : Visibility → Abs Term         → Term
  var     : Nat → List (Arg Term)         → Term
  meta    : Meta → List (Arg Term)        → Term    
  def     : Name → List (Arg Term)        → Term
  pat     : List Clause → List (Arg Term) → Term
  unknown :                                 Term

{-# BUILTIN AGDATERM Term #-}

pattern vlam s t = lam visible (abs s t)
pattern hlam s t = lam hidden  (abs s t)

pattern vpi s a b = pi (varg a) (abs s b)
pattern hpi s a b = pi (harg a) (abs s b)

data Sort where
  set      : Term → Sort
  lit-set  : Nat  → Sort
  prop     : Term → Sort
  lit-prop : Nat  → Sort
  inf      : Nat  → Sort
  unknown  :        Sort

{-# BUILTIN AGDASORT Sort #-}

data Pattern where
  con    : Name → List (Arg Pattern) → Pattern
  dot    : Term                      → Pattern
  var    : Nat                       → Pattern
  lit    : Literal                   → Pattern
  proj   : Name                      → Pattern
  absurd : Nat                       → Pattern

{-# BUILTIN AGDAPATTERN Pattern #-}

Telescope = List (String × Arg Term)

data Clause where
  clause : Telescope → List (Arg Pattern) → Term → Clause
  absurd : Telescope → List (Arg Pattern)        → Clause

{-# BUILTIN AGDACLAUSE Clause #-}
