module Prelude.Reflection.Error where
open import Prelude.Prim
open import Prelude.Reflection.Name
open import Prelude.Reflection.Term

data Error : Type where
  name : Name    → Error
  pat  : Pattern → Error
  str  : String  → Error
  term : Term    → Error

{-# BUILTIN AGDAERRORPART       Error #-}
{-# BUILTIN AGDAERRORPARTNAME   name  #-}
{-# BUILTIN AGDAERRORPARTPATT   pat   #-}
{-# BUILTIN AGDAERRORPARTSTRING str   #-}
{-# BUILTIN AGDAERRORPARTTERM   term  #-}

