module Prelude.Reflection where
open import Prelude.Prim
open import Prelude.Reflection.Argument public
open import Prelude.Reflection.Error    public
open import Prelude.Reflection.Literal  public
open import Prelude.Reflection.Meta     public
open import Prelude.Reflection.Monad    public
open import Prelude.Reflection.Name     public
open import Prelude.Reflection.Solver   public
open import Prelude.Reflection.Term     public

all-metas-in : Term → List Blocker
all-metas-in t = go t [] where
  go  : Term → List Blocker → List Blocker
  go* : List (Arg Term) → List Blocker → List Blocker

  go (meta x args) acc = go* args (meta x ∷ acc)  
  go (var  _ args) acc = go* args acc
  go (con  _ args) acc = go* args acc
  go (def  _ args) acc = go* args acc
  go (pi (arg _ a) (abs _ b)) acc = go a (go b acc)
  go (lam _        (abs _ t)) acc = go t acc
  go (lit  _)      acc = acc
  go (sort _)      acc = acc
  go (pat-lam _ _) acc = acc
  go unknown       acc = acc
  
  go* [] acc = acc
  go* (arg _ x ∷ xs) acc = go x (go* xs acc)

wait-for-type : Term → TC Term
wait-for-type t with all-metas-in t
...| [] = return t
...| ts = block (all ts)

“refl” : Term
“refl” = def (quote ≡-refl) []
