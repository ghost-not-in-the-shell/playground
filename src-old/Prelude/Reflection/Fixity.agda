module Prelude.Reflection.Fixity where
open import Prelude.Float

data Assoc : Set where
  left-assoc  : Assoc
  right-assoc : Assoc
  non-assoc   : Assoc

{-# BUILTIN ASSOC      Assoc       #-}
{-# BUILTIN ASSOCLEFT  left-assoc  #-}
{-# BUILTIN ASSOCRIGHT right-assoc #-}
{-# BUILTIN ASSOCNON   non-assoc   #-}

data Precedence : Set where
  related   : Float → Precedence
  unrelated :         Precedence

{-# BUILTIN PRECEDENCE    Precedence #-}
{-# BUILTIN PRECRELATED   related    #-}
{-# BUILTIN PRECUNRELATED unrelated  #-}

data Fixity : Set where
  fixity : Assoc → Precedence → Fixity

{-# BUILTIN FIXITY       Fixity #-}
{-# BUILTIN FIXITYFIXITY fixity #-}
