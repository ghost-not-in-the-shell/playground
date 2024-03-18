module Prelude.Reflection.Argument where
open import Prelude.List

data Visibility : Set where
  visible   : Visibility
  hidden    : Visibility
  instance' : Visibility

{-# BUILTIN HIDING   Visibility #-}
{-# BUILTIN VISIBLE  visible    #-}
{-# BUILTIN HIDDEN   hidden     #-}
{-# BUILTIN INSTANCE instance'  #-}

data Relevance : Set where
  relevant   : Relevance
  irrelevant : Relevance

{-# BUILTIN RELEVANCE  Relevance  #-}
{-# BUILTIN RELEVANT   relevant   #-}
{-# BUILTIN IRRELEVANT irrelevant #-}

data Quantity : Set where
  quantity-0 : Quantity
  quantity-ω : Quantity

{-# BUILTIN QUANTITY   Quantity   #-}
{-# BUILTIN QUANTITY-0 quantity-0 #-}
{-# BUILTIN QUANTITY-ω quantity-ω #-}

data Modality : Set where
  modality : Relevance → Quantity → Modality

{-# BUILTIN MODALITY             Modality #-}
{-# BUILTIN MODALITY-CONSTRUCTOR modality #-}

pattern default-modality = modality relevant quantity-ω

data ArgInfo : Set where
  arg-info : Visibility → Modality → ArgInfo

{-# BUILTIN ARGINFO    ArgInfo  #-}
{-# BUILTIN ARGARGINFO arg-info #-}

data Arg (A : Set) : Set where
  arg : ArgInfo → A → Arg A

{-# BUILTIN ARG    Arg #-}
{-# BUILTIN ARGARG arg #-}

pattern varg t = arg (arg-info visible   default-modality) t
pattern harg t = arg (arg-info hidden    default-modality) t
pattern iarg t = arg (arg-info instance' default-modality) t

pattern _v∷_ x args = varg x ∷ args
pattern _h∷_ x args = harg  x ∷ args
