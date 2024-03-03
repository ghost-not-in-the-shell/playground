module Prelude.Reflection.Definition where
open import Prelude.List
open import Prelude.Nat
open import Prelude.Reflection.Argument
open import Prelude.Reflection.Name
open import Prelude.Reflection.Term

data Definition : Set where
  function    : List Clause → Definition
  data-type   : Nat → List Name → Definition
  data-con    : Name → Definition
  record-type : Name → List (Arg Name) → Definition
  axiom       : Definition
  prim-fun    : Definition

{-# BUILTIN AGDADEFINITION                Definition  #-}
{-# BUILTIN AGDADEFINITIONFUNDEF          function    #-}
{-# BUILTIN AGDADEFINITIONDATADEF         data-type   #-}
{-# BUILTIN AGDADEFINITIONDATACONSTRUCTOR data-con    #-}
{-# BUILTIN AGDADEFINITIONRECORDDEF       record-type #-}
{-# BUILTIN AGDADEFINITIONPOSTULATE       axiom       #-}
{-# BUILTIN AGDADEFINITIONPRIMITIVE       prim-fun    #-}
