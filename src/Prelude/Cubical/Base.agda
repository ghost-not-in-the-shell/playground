module Prelude.Cubical.Base where
open import Prelude.Prim
open import Prelude.Idiom hiding (refl; sym; trans)

private
  refl : ∀ {A} {a : A} → a ≡ a
  refl {a = a} = λ i → a

  sym : ∀ {A} {a₀ a₁ : A} → a₀ ≡ a₁ → a₁ ≡ a₀
  sym a = λ i → a (~ i)

symP : {A : 𝕀 → Type} {a₀ : A i0} {a₁ : A i1}
  → a₀ ≡ a₁ [ i ↦ A    i ]
  → a₁ ≡ a₀ [ i ↦ A (~ i)]
symP a = λ i → a (~ i)

cong : ∀ {A B} (f : A → B) {a₀ a₁} → a₀ ≡ a₁ → f a₀ ≡ f a₁
cong f a = λ i → f (a i)

cong₂ : ∀ {A B C} (f : A → B → C) {a₀ a₁ b₀ b₁}
  → a₀ ≡ a₁ → b₀ ≡ b₁ → f a₀ b₀ ≡ f a₁ b₁
cong₂ f a b = λ i → f (a i) (b i)

ap : ∀ {A} {B : A → Type} (f : (x : A) → B x) {a₀ a₁}
  → (a : a₀ ≡ a₁) → f a₀ ≡ f a₁ [ i ↦ B (a i)]
ap f a = λ i → f (a i)

ap₂ : ∀ {A} {B : A → Type} {C : (x : A) → B x → Type}
  → (f : (x : A) (y : B x) → C x y)
  → {a₀ a₁ : A} {b₀ : B a₀} {b₁ : B a₁}
  → (a : a₀ ≡ a₁) (b : b₀ ≡ b₁ [ i ↦ B (a i)])
  → f a₀ b₀ ≡ f a₁ b₁ [ i ↦ C (a i) (b i)]
ap₂ f a b = λ i → f (a i) (b i)

apd : {A : 𝕀 → Type} {B : ∀ i → A i → Type}
  → {a₀ : A i0} {a₁ : A i1}
  → (f : ∀ i (x : A i) → B i x)
  → (a : a₀ ≡      a₁ [ i ↦ A i      ])
  → f i0 a₀ ≡ f i1 a₁ [ i ↦ B i (a i)]
apd f a = λ i → f i (a i)

pure : ∀ {A} (a : A) → a ≡ a
pure _ = refl

module ApplicativeReasoning where
  infixl 4 _<*>_
  _<*>_ : ∀ {A B} {f₀ f₁ : A → B} {a₀ a₁}
    → (f : f₀ ≡    f₁)
    → (a : a₀ ≡    a₁)
    →   f₀ a₀ ≡ f₁ a₁
  f <*> a = λ i → f i (a i)

module ApplicativeP where
  infixl 4 _<*>_
  _<*>_ : ∀ {A₀ A₁} {B₀ : A₀ → Type} {B₁ : A₁ → Type}
    → {f₀ : (x : A₀) → B₀ x} {f₁ : (x : A₁) → B₁ x} {a₀ : A₀} {a₁ : A₁}
    → {A : A₀ ≡    A₁}
    → {B : B₀ ≡    B₁ [ i ↦ (A i → Type)        ]}
    → (f : f₀ ≡    f₁ [ i ↦ ((x : A i) → B i x) ])
    → (a : a₀ ≡    a₁ [ i ↦ A i                 ])
    →   f₀ a₀ ≡ f₁ a₁ [ i ↦ B i (a i)           ]
  f <*> a = apd (λ i → f i) a

coe : ∀ {A₀ A₁} → A₀ ≡ A₁ → A₀ → A₁
coe A a = transp (λ i → A i) i0 a

subst : ∀ {A} (P : A → Type) {a₀ a₁} → a₀ ≡ a₁ → P a₀ → P a₁
subst P a u = coe (cong P a) u

subst₂ : ∀ {A} {B : A → Type} (P : (x : A) → B x → Type)
  → {a₀ a₁ : A} {b₀ : B a₀} {b₁ : B a₁}
  → (a : a₀ ≡ a₁)
  → (b : b₀ ≡ b₁ [ i ↦ B (a i)])
  → P a₀ b₀
  → P a₁ b₁
subst₂ P a b u = coe (ap₂ P a b) u

Square : ∀ {A} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  → (a₀₋ : a₀₀ ≡ a₀₁)
  → (a₁₋ : a₁₀ ≡ a₁₁)
  → (a₋₀ : a₀₀ ≡ a₁₀)
  → (a₋₁ : a₀₁ ≡ a₁₁)
  → Type
Square a₀₋ a₁₋ a₋₀ a₋₁ = a₀₋ ≡ a₁₋ [ i ↦ a₋₀ i ≡ a₋₁ i ]

SquareP : (A : 𝕀 → 𝕀 → Type)
  → {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₁₀ : A i1 i0} {a₁₁ : A i1 i1}
  → (a₀₋ : a₀₀ ≡ a₀₁ [ j ↦ A i0 j ])
  → (a₁₋ : a₁₀ ≡ a₁₁ [ j ↦ A i1 j ])
  → (a₋₀ : a₀₀ ≡ a₁₀ [ i ↦ A i i0 ])
  → (a₋₁ : a₀₁ ≡ a₁₁ [ i ↦ A i i1 ])
  → Type
SquareP A a₀₋ a₁₋ a₋₀ a₋₁ = a₀₋ ≡ a₁₋ [ i ↦ a₋₀ i ≡ a₋₁ i [ j ↦ A i j ] ]

trans₃ : ∀ {A} {a b c d : A} → a ≡ b → b ≡ c → c ≡ d → a ≡ d
trans₃ p q r = λ i → hcomp (λ { j (i = i0) → sym p j
                              ; j (i = i1) →     r j })
                           (q i)

private
  trans : ∀ {A} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
  trans = trans₃ refl

trans₃-filler : ∀ {A} {a b c d : A}
  → (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
  → Square (sym p) r q (trans₃ p q r)
trans₃-filler p q r = λ i j → hcomp (λ { k (i = i0) → sym p (j ∧ k)
                                       ; k (i = i1) →     r (j ∧ k)
                                       ; k (j = i0) →     q i })
                                    (q i)

trans-filler : ∀ {A} {a b c : A}
  → (p : a ≡ b) (q : b ≡ c)
  → Square refl q p (trans p q)
trans-filler = trans₃-filler refl

transP₃ : ∀ {A} (B : A → Type) {a b c d}
  → {a' : B a} {b' : B b} {c' : B c} {d' : B d}
  → {p : a ≡ b} {q : b ≡ c} {r : c ≡ d}
  → a' ≡ b' [ i ↦ B (p i)]
  → b' ≡ c' [ i ↦ B (q i)]
  → c' ≡ d' [ i ↦ B (r i)]
  → a' ≡ d' [ i ↦ B (trans₃ p q r i)]
transP₃ B {p = p} {q} {r} p' q' r' = λ i →
  comp (λ j → B (trans₃-filler p q r i j))
       (λ { j (i = i0) → symP p' j
          ; j (i = i1) →      r' j })
       (q' i)

transP : ∀ {A} (B : A → Type) {a b c}
  → {a' : B a} {b' : B b} {c' : B c}
  → {p : a ≡ b} {q : b ≡ c}
  → a' ≡ b' [ i ↦ B (p i)]
  → b' ≡ c' [ i ↦ B (q i)]
  → a' ≡ c' [ i ↦ B (trans p q i)]
transP B = transP₃ B refl

instance
  ≡-equiv : ∀ {A} → EquivRel {I = ⊤} (λ tt → A) _≡_
  ≡-equiv = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }

module ≡-Reasoning where
  private variable
    A : Type
    x y z : A

  infixr 2 ≡⟨⟩ ≡⟨⟨

  ≡⟨⟩ : ∀ x → y ≡ z → x ≡ y → x ≡ z
  ≡⟨⟩ = ≈⟨⟩

  ≡⟨⟨ : ∀ x → y ≡ z → y ≡ x → x ≡ z
  ≡⟨⟨ = ≈⟨⟨

  syntax ≡⟨⟩ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z
  syntax ≡⟨⟨ x y≡z y≡x = x ≡⟨ y≡x ⟨ y≡z

open ≡-Reasoning public

module Coersion (A : 𝕀 → Type) where
  coe0→1 : A i0 → A i1
  coe0→1 a₀ = transp (λ i → A i) i0 a₀

  coe1→0 : A i1 → A i0
  coe1→0 a₁ = transp (λ i → A (~ i)) i0 a₁

  coe0→i : (i : 𝕀) → A i0 → A i
  coe0→i i a₀ = transp (λ j → A (i ∧ j)) (~ i) a₀

  coe1→i : (i : 𝕀) → A i1 → A i
  coe1→i i a₁ = transp (λ j → A (i ∨ ~ j)) i a₁

  coei→0 : (i : 𝕀) → A i → A i0
  coei→0 i a = transp (λ j → A (i ∧ ~ j)) (~ i) a

  coei→1 : (i : 𝕀) → A i → A i1
  coei→1 i a = transp (λ j → A (i ∨ j)) i a

open Coersion public

module _ {A : 𝕀 → Type} {a₀ : A i0} {a₁ : A i1} where
  to-PathP : coe0→1 A a₀ ≡ a₁ → a₀ ≡ a₁ [ i ↦ A i ]
  to-PathP a = λ i → hcomp (λ { j (i = i0) → a₀
                              ; j (i = i1) → a j })
                           (coe0→i A i a₀)

  from-PathP : a₀ ≡ a₁ [ i ↦ A i ] → coe0→1 A a₀ ≡ a₁
  from-PathP a = λ i → transp (λ j → A (i ∨ j)) i (a i)

module _ (A : 𝕀 → Type) (a₀ : A i0) (a₁ : A i1) where
  PathP≡Path0→1 : PathP A a₀ a₁ ≡ Path (A i1) (coe0→1 A a₀) a₁
  PathP≡Path0→1 i = coe0→i A i a₀ ≡ a₁ [ j ↦ A (i ∨ j)]

  PathP≡Path1→0 : PathP A a₀ a₁ ≡ Path (A i0) a₀ (coe1→0 A a₁)
  PathP≡Path1→0 i = a₀ ≡ coe1→i A (~ i) a₁ [ j ↦ A (~ i ∧ j) ]
