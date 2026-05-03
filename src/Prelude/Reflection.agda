module Prelude.Reflection where
open import Prelude.Prim
open import Prelude.Idiom
open import Agda.Builtin.Reflection public
  renaming ( returnTC  to return )

pattern default-modality = modality relevant quantity-ω

pattern argᵥ x = arg (arg-info visible   default-modality) x
pattern argₕ x = arg (arg-info hidden    default-modality) x
pattern argᵢ x = arg (arg-info instance′ default-modality) x

infixr 5 _∷ᵥ_ _∷ₕ_ _∷ᵢ_
pattern _∷ᵥ_ x xs = argᵥ x ∷ xs
pattern _∷ₕ_ x xs = argₕ x ∷ xs
pattern _∷ᵢ_ x xs = argᵢ x ∷ xs

infixl 1 _>>=_
_>>=_ = bindTC

infixl 3 _<|>_
_<|>_ = catchTC

all-metas-in : Term → List Blocker
all-metas-in t = go t [] where
  go  : Term → List Blocker → List Blocker
  go* : List (Arg Term) → List Blocker → List Blocker

  go (meta x args) acc = go* args (blockerMeta x ∷ acc)  
  go (var  _ args) acc = go* args acc
  go (con  _ args) acc = go* args acc
  go (def  _ args) acc = go* args acc
  go (pi (arg _ a) (abs _ b)) acc = go a (go b acc)
  go (lam _        (abs _ t)) acc = go t acc
  go (lit  _)      acc = acc
  go (agda-sort _) acc = acc
  go (pat-lam _ _) acc = acc
  go unknown       acc = acc
  
  go* [] acc = acc
  go* (arg _ x ∷ xs) acc = go x (go* xs acc)

wait-for-type : Term → TC Term
wait-for-type t with all-metas-in t
...| [] = return t
...| ts = blockTC (blockerAll ts)

“refl” : Term
“refl” = def (quote refl) []
