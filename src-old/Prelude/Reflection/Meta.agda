module Prelude.Reflection.Meta where
open import Prelude.List

postulate Meta : Set

{-# BUILTIN AGDAMETA Meta #-}

data Blocker : Set where
  meta : Meta         → Blocker
  all  : List Blocker → Blocker  
  any  : List Blocker → Blocker

{-# BUILTIN AGDABLOCKER     Blocker #-}
{-# BUILTIN AGDABLOCKERMETA meta    #-}
{-# BUILTIN AGDABLOCKERALL  all     #-}
{-# BUILTIN AGDABLOCKERANY  any     #-}
