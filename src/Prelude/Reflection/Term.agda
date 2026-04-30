module Prelude.Reflection.Term where
open import Prelude.Prim
open import Prelude.Reflection.Argument
open import Prelude.Reflection.Literal
open import Prelude.Reflection.Meta
open import Prelude.Reflection.Name

data Abs {ℓ} (A : Type ℓ) : Type where
  abs : String → A → Abs A

{-# BUILTIN ABS    Abs #-}
{-# BUILTIN ABSABS abs #-}

data Term    : Type
data Sort    : Type
data Pattern : Type
data Clause  : Type

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

pattern piᵥ s a b = pi (argᵥ a) (abs s b)
pattern piₕ s a b = pi (argₕ a) (abs s b)
pattern piᵢ s a b = pi (argᵢ a) (abs s b)

pattern lamᵥ s t = lam expl (abs s t)
pattern lamₕ s t = lam impl (abs s t)
pattern lamᵢ s t = lam inst (abs s t)

data Sort where
  set      : Term → Sort
  lit-set  : Nat  → Sort
  inf-set  : Nat  → Sort
  prop     : Term → Sort
  lit-prop : Nat  → Sort
  unknown  :        Sort

data Pattern where
  con    : Name → List (Arg Pattern) → Pattern
  absurd : Nat     → Pattern  
  dot    : Term    → Pattern
  lit    : Literal → Pattern
  proj   : Name    → Pattern
  var    : Nat     → Pattern

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

{-# BUILTIN AGDAPATCON    con    #-}
{-# BUILTIN AGDAPATABSURD absurd #-}
{-# BUILTIN AGDAPATDOT    dot    #-}
{-# BUILTIN AGDAPATLIT    lit    #-}
{-# BUILTIN AGDAPATPROJ   proj   #-}
{-# BUILTIN AGDAPATVAR    var    #-}

{-# BUILTIN AGDACLAUSEABSURD absurd #-}
{-# BUILTIN AGDACLAUSECLAUSE clause #-}

data Definition : Type where
  function    : List Clause            → Definition
  data-type   : Nat → List Name        → Definition
  data-con    : Name → Quantity        → Definition
  record-type : Name → List (Arg Name) → Definition
  axiom       :                          Definition
  prim-fun    :                          Definition

{-# BUILTIN AGDADEFINITION                Definition  #-}
{-# BUILTIN AGDADEFINITIONFUNDEF          function    #-}
{-# BUILTIN AGDADEFINITIONDATADEF         data-type   #-}
{-# BUILTIN AGDADEFINITIONDATACONSTRUCTOR data-con    #-}
{-# BUILTIN AGDADEFINITIONRECORDDEF       record-type #-}
{-# BUILTIN AGDADEFINITIONPOSTULATE       axiom       #-}
{-# BUILTIN AGDADEFINITIONPRIMITIVE       prim-fun    #-}
