module Prelude.Reflection.Argument where
open import Prelude.List

data Visibility : Set where
  explicit  : Visibility
  implicit  : Visibility
  instance' : Visibility

{-# BUILTIN HIDING   Visibility #-}
{-# BUILTIN VISIBLE  explicit   #-}
{-# BUILTIN HIDDEN   implicit   #-}
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

pattern varg x = arg (arg-info explicit  default-modality) x
pattern harg x = arg (arg-info implicit  default-modality) x
pattern iarg x = arg (arg-info instance' default-modality) x

infixr 5 _v∷_ _h∷_ _i∷_
pattern _v∷_ x xs = varg x ∷ xs
pattern _h∷_ x xs = harg x ∷ xs
pattern _i∷_ x xs = iarg x ∷ xs
