module Prelude.Reflection.Meta where
open import Prelude.Prim

postulate Meta : Type

{-# BUILTIN AGDAMETA Meta #-}

data Blocker : Type where
  meta : Meta → Blocker
  all  : List Blocker → Blocker
  any  : List Blocker → Blocker

{-# BUILTIN AGDABLOCKER     Blocker #-}
{-# BUILTIN AGDABLOCKERMETA meta    #-}
{-# BUILTIN AGDABLOCKERALL  all     #-}
{-# BUILTIN AGDABLOCKERANY  any     #-}
