module Prelude.Cubical.HLevel where
open import Prelude.Prim
open import Prelude.Idiom
open import Prelude.Cubical.Base

private variable
  A B : Type
  P : A → Type

record is-contr (A : Type) : Type where
  constructor _,_
  field
    centre : A
    connect : ∀ x → centre ≡ x

open is-contr public

is-prop : Type → Type
is-prop A = (x y : A) → x ≡ y

is-set : Type → Type
is-set A = (x y : A) (p q : x ≡ y) → Square p q refl refl

is-hlevel : Type → Nat → Type
is-hlevel A 0 = is-contr A
is-hlevel A 1 = is-prop  A
is-hlevel A (suc (suc n)) = (x y : A) → is-hlevel (x ≡ y) (suc n)

private
  _ : is-set A ≡ is-hlevel A 2
  _ = refl

is-prop→is-set : is-prop A → is-set A
is-prop→is-set path x y p q = λ i j →
  hcomp (λ { k (i = i0) → path x (p j) k
           ; k (i = i1) → path x (q j) k
           ; k (j = i0) → path x x     k
           ; k (j = i1) → path x y     k })
        x

is-contr→is-prop : is-contr A → is-prop A
is-contr→is-prop (centre , connect) x y = λ i →
  hcomp (λ { j (i = i0) → connect x j
           ; j (i = i1) → connect y j })
        centre

is-hlevel-suc : ∀ n → is-hlevel A n → is-hlevel A (suc n)
is-hlevel-suc 0 = is-contr→is-prop
is-hlevel-suc 1 = is-prop→is-set
is-hlevel-suc (suc (suc n)) h x y = is-hlevel-suc (suc n) (h x y)

is-hlevel-+ : ∀ n k → is-hlevel A n → is-hlevel A (k + n)
is-hlevel-+ n zero = id
is-hlevel-+ n (suc k) h = is-hlevel-suc (k + n) (is-hlevel-+ n k h)

Path-is-hlevel : ∀ n → is-hlevel A (suc n) → ∀ x y → is-hlevel (Path A x y) n
Path-is-hlevel 0 path x y = record
  { centre = path x y
  ; connect = λ p → is-prop→is-set path x y (path x y) p 
  }
Path-is-hlevel (suc n) ncube x y = ncube x y

PathP-is-hlevel : {A : 𝕀 → Type} (n : Nat) → is-hlevel (A i1) (suc n)
  → ∀ x y → is-hlevel (PathP A x y) n
PathP-is-hlevel {A = A} n ncube x y =
  subst (λ - → is-hlevel - n) (sym (PathP≡Path0→1 A x y))
    $ Path-is-hlevel n ncube (coe0→1 A x) y

is-prop∙→is-contr : is-prop A → A → is-contr A
is-prop∙→is-contr path x = record
  { centre  = x
  ; connect = λ y → path x y
  }

is-prop-is-prop : is-prop (is-prop A)
is-prop-is-prop path₁ path₂ = λ i x y →
  is-prop→is-set path₁ x y (path₁ x y) (path₂ x y) i

is-contr-is-prop : is-prop (is-contr A)
is-contr-is-prop (c₁ , p₁) (c₂ , p₂) = λ i → record
  { centre  = p₁ c₂ i
  ; connect = λ x j →
    hcomp (λ { k (i = i0) → p₁ (p₁ x  j) k
             ; k (i = i1) → p₁ (p₂ x  j) k
             ; k (j = i0) → p₁ (p₁ c₂ i) k
             ; k (j = i1) → p₁ x         k })
          c₁
  }

is-hlevel-is-prop : ∀ n → is-prop (is-hlevel A n)
is-hlevel-is-prop 0 = is-contr-is-prop
is-hlevel-is-prop 1 = is-prop-is-prop
is-hlevel-is-prop (suc (suc n)) ncube₁ ncube₂ = λ i x y →
  is-hlevel-is-prop (suc n) (ncube₁ x y) (ncube₂ x y) i

is-prop→PathP : {A : 𝕀 → Type} → ((i : 𝕀) → is-prop (A i))
  → ∀ a₀ a₁ → a₀ ≡ a₁ [ i ↦ A i ]
is-prop→PathP {A = A} path a₀ a₁ = to-PathP $ path i1 (coe0→1 A a₀) a₁

is-contr→extend : is-contr A → (φ : 𝔽) (u : Partial φ A) → A [ φ ↦ u ]
is-contr→extend (centre , connect) φ u = inS do
  hcomp (λ { i (φ = i0) → centre
           ; i (φ = i1) → connect (u always) i })
        centre

extend→is-contr : ((φ : 𝔽) (u : Partial φ A) → A [ φ ↦ u ]) → is-contr A
extend→is-contr extend = record
  { centre  =         outS (extend i0 λ ())
  ; connect = λ x i → outS (extend i  λ { (i = i1) → x })
  }

retract→is-contr : (f : A → B) (g : B → A) (retract : ∀ x → f (g x) ≡ x)
  → is-contr A → is-contr B
retract→is-contr f g r (centre , connect) = record
  { centre = f centre
  ; connect = λ x → begin
    f centre ≡⟨ ap f (connect (g x)) ⟩
    f(g x)   ≡⟨ r x ⟩
        x    ∎
  }

retract→is-prop : (f : A → B) (g : B → A) (retract : ∀ x → f (g x) ≡ x)
  → is-prop A → is-prop B
retract→is-prop f g r path = λ x y i →
  hcomp
    (λ { j (i = i0) → r x j
       ; j (i = i1) → r y j })
    (f (path (g x) (g y) i))

retract→is-set : (f : A → B) (g : B → A) (retract : ∀ x → f (g x) ≡ x)
  → is-set A → is-set B
retract→is-set f g r square = λ x y p q i j →
  hcomp
    (λ { k (i = i0) → r (p j) k
       ; k (i = i1) → r (q j) k
       ; k (j = i0) → r x k
       ; k (j = i1) → r y k })
    (f (square (g x) (g y) (ap g p) (ap g q) i j))

retract→is-hlevel : ∀ n (f : A → B) (g : B → A) (retract : ∀ x → f (g x) ≡ x)
  → is-hlevel A n → is-hlevel B n
retract→is-hlevel 0 = retract→is-contr
retract→is-hlevel 1 = retract→is-prop
retract→is-hlevel (suc (suc n)) f g r ncube = λ x y →
  retract→is-hlevel (suc n)
    (λ ncube i → hcomp (λ { j (i = i0) → r x j
                          ; j (i = i1) → r y j })
                       (f (ncube i)))
    (ap g)
    (λ ncube i j → hcomp (λ { k (i = i1) → ncube j
                            ; k (j = i0) → r x (i ∨ k)
                            ; k (j = i1) → r y (i ∨ k) })
                         (r (ncube j) i))
    (ncube (g x) (g y))

iso→is-hlevel : ∀ n → A ≅ B → is-hlevel A n → is-hlevel B n
iso→is-hlevel n (fwd f) h =
  retract→is-hlevel n f (f ⁻¹) (λ x → ap (_$ x) (∘-invʳ f)) h

iso→is-set : A ≅ B → is-set A → is-set B
iso→is-set = iso→is-hlevel 2

Π-is-contr : (∀ x → is-contr (P x)) → is-contr (∀ x → P x)
Π-is-contr h = record
  { centre  = λ x → h x .centre
  ; connect = λ f i x → h x .connect (f x) i
  }

Π-is-prop : (∀ x → is-prop (P x)) → is-prop (∀ x → P x)
Π-is-prop path = λ f g i x → path x (f x) (g x) i

Π-is-set : (∀ x → is-set (P x)) → is-set (∀ x → P x)
Π-is-set square = λ f g p q i j x → square x (f x) (g x) (ap (_$ x) p) (ap (_$ x) q) i j

Π-Path-intro : {f g : ∀ x → P x} → (∀ x → f x ≡ g x) → f ≡ g
Π-Path-intro p i x = p x i

Π-Path-elim : {f g : ∀ x → P x} → f ≡ g → (∀ x → f x ≡ g x)
Π-Path-elim p x i = p i x

Π-Path-iso : {f g : ∀ x → P x} → (∀ x → f x ≡ g x) ≅ (f ≡ g)
Π-Path-iso = record
  { fwd = Π-Path-intro
  ; iso = record
    { bwd = Π-Path-elim
    ; ∘-invˡ = refl
    ; ∘-invʳ = refl
    }
  }

Π-is-hlevel : ∀ n → (∀ x → is-hlevel (P x) n) → is-hlevel (∀ x → P x) n
Π-is-hlevel 0 = Π-is-contr
Π-is-hlevel 1 = Π-is-prop
Π-is-hlevel (suc (suc n)) ncube = λ f g →
  let fwd : (∀ x → f x ≡ g x) → f ≡ g
      fwd p i x = p x i

      bwd : f ≡ g → ∀ x → f x ≡ g x
      bwd p x i = p i x
  in iso→is-hlevel (suc n) Π-Path-iso
       (Π-is-hlevel (suc n) λ x → ncube x (f x) (g x))

Σ-is-contr : is-contr A → (∀ x → is-contr (P x)) → is-contr (Σ A P)
Σ-is-contr {P = P} (c , p) h = record
  { centre  = c , (h c) .centre
  ; connect = λ (x , y) i →
    (p x i , (h (p x i)) .connect (transp (λ j → P (p x (i ∨ ~ j))) i y) i )
  }

Σ-is-prop : is-prop A → (∀ x → is-prop (P x)) → is-prop (Σ A P)
Σ-is-prop path₁ path₂ = λ (a₀ , b₀) (a₁ , b₁) i →
  ( path₁ a₀ a₁ i
  , is-prop→PathP (λ i → path₂ (path₁ a₀ a₁ i)) b₀ b₁ i)

Σ-Path-intro : {x y : Σ A P} → Σ[ p ∈ fst x ≡ fst y ] (snd x ≡ snd y [ i ↦ P (p i)]) → x ≡ y
Σ-Path-intro (p , q) = λ i → (p i , q i)

Σ-Path-elim : {x y : Σ A P} → x ≡ y → Σ[ p ∈ fst x ≡ fst y ] (snd x ≡ snd y [ i ↦ P (p i)])
Σ-Path-elim p = (λ i → fst (p i)) , λ i → snd (p i)

Σ-Path-iso : {x y : Σ A P} → (Σ[ p ∈ fst x ≡ fst y ] (snd x ≡ snd y [ i ↦ P (p i)])) ≅ (x ≡ y)
Σ-Path-iso = record
  { fwd = Σ-Path-intro
  ; iso = record
    { bwd = Σ-Path-elim
    ; ∘-invˡ = refl
    ; ∘-invʳ = refl
    }
  }

Σ-is-hlevel : ∀ n → is-hlevel A n → (∀ x → is-hlevel (P x) n) → is-hlevel (Σ A P) n
Σ-is-hlevel 0 = Σ-is-contr
Σ-is-hlevel 1 = Σ-is-prop
Σ-is-hlevel (suc (suc n)) ncube₁ ncube₂ (x₀ , y₀) (x₁ , y₁) =
  iso→is-hlevel (suc n) Σ-Path-iso
    $ Σ-is-hlevel (suc n)
        (ncube₁ x₀ x₁)
        (λ _ → PathP-is-hlevel (suc n) (ncube₂ x₁) y₀ y₁)

×-is-hlevel : ∀ n → is-hlevel A n → is-hlevel B n → is-hlevel (A × B) n
×-is-hlevel n ncube₁ ncube₂ = Σ-is-hlevel n ncube₁ (const ncube₂)

Σ-is-set : is-set A → (∀ x → is-set (P x)) → is-set (Σ A P)
Σ-is-set = Σ-is-hlevel 2

×-is-set : is-set A → is-set B → is-set (A × B)
×-is-set = ×-is-hlevel 2
