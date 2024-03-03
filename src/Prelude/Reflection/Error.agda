module Prelude.Reflection.Error where
open import Prelude.String
open import Prelude.Reflection.Name
open import Prelude.Reflection.Term

data Error : Set where
  name : Name    → Error
  pat  : Pattern → Error
  str  : String  → Error
  term : Term    → Error

{-# BUILTIN AGDAERRORPART       Error #-}
{-# BUILTIN AGDAERRORPARTNAME   name  #-}
{-# BUILTIN AGDAERRORPARTPATT   pat   #-}
{-# BUILTIN AGDAERRORPARTSTRING str   #-}
{-# BUILTIN AGDAERRORPARTTERM   term  #-}
