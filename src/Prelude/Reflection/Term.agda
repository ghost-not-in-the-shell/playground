module Prelude.Reflection.Term where
open import Prelude.Equality
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

{-# BUILTIN ABS    Abs #-}
{-# BUILTIN ABSABS abs #-}

data Term    : Set
data Sort    : Set
data Pattern : Set
data Clause  : Set

data Term where
  lit     : Literal → Term
  sort    : Sort    → Term
  pi      : Arg Term   → Abs Term → Term
  lam     : Visibility → Abs Term → Term
  pat-lam : List Clause → List (Arg Term) → Term
  var     : Nat  → List (Arg Term) → Term
  meta    : Meta → List (Arg Term) → Term
  con     : Name → List (Arg Term) → Term
  def     : Name → List (Arg Term) → Term
  unknown : Term

pattern vpi s a b = pi (varg a) (abs s b)
pattern hpi s a b = pi (harg a) (abs s b)
pattern ipi s a b = pi (iarg a) (abs s b)

pattern vlam s t = lam explicit  (abs s t)
pattern hlam s t = lam implicit  (abs s t)
pattern ilam s t = lam instance' (abs s t)

data Sort where
  set      : Term → Sort
  lit-set  : Nat  → Sort
  inf-set  : Nat  → Sort
  prop     : Term → Sort
  lit-prop : Nat  → Sort
  unknown  : Sort

data Pattern where
  absurd : Nat → Pattern
  con    : Name → List (Arg Pattern) → Pattern
  dot    : Term → Pattern
  lit    : Literal → Pattern
  proj   : Name → Pattern
  var    : Nat → Pattern

Telescope = List (Σ String λ _ → Arg Term)

data Clause where
  absurd : Telescope → List (Arg Pattern) → Clause
  clause : Telescope → List (Arg Pattern) → Term → Clause

{-# BUILTIN AGDATERM    Term    #-}
{-# BUILTIN AGDASORT    Sort    #-}
{-# BUILTIN AGDAPATTERN Pattern #-}
{-# BUILTIN AGDACLAUSE  Clause  #-}

{-# BUILTIN AGDATERMLIT         lit     #-}
{-# BUILTIN AGDATERMSORT        sort    #-}
{-# BUILTIN AGDATERMPI          pi      #-}
{-# BUILTIN AGDATERMLAM         lam     #-}
{-# BUILTIN AGDATERMEXTLAM      pat-lam #-}
{-# BUILTIN AGDATERMVAR         var     #-}
{-# BUILTIN AGDATERMMETA        meta    #-}
{-# BUILTIN AGDATERMCON         con     #-}
{-# BUILTIN AGDATERMDEF         def     #-}
{-# BUILTIN AGDATERMUNSUPPORTED unknown #-}

{-# BUILTIN AGDASORTSET         set      #-}
{-# BUILTIN AGDASORTLIT         lit-set  #-}
{-# BUILTIN AGDASORTINF         inf-set  #-}
{-# BUILTIN AGDASORTPROP        prop     #-}
{-# BUILTIN AGDASORTPROPLIT     lit-prop #-}
{-# BUILTIN AGDASORTUNSUPPORTED unknown  #-}

{-# BUILTIN AGDAPATABSURD absurd #-}
{-# BUILTIN AGDAPATCON    con    #-}
{-# BUILTIN AGDAPATDOT    dot    #-}
{-# BUILTIN AGDAPATLIT    lit    #-}
{-# BUILTIN AGDAPATPROJ   proj   #-}
{-# BUILTIN AGDAPATVAR    var    #-}

{-# BUILTIN AGDACLAUSEABSURD absurd #-}
{-# BUILTIN AGDACLAUSECLAUSE clause #-}
