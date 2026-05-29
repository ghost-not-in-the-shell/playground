module Prelude.Cubical.HLevel where
open import Prelude.Prim
open import Prelude.Idiom
open import Prelude.Cubical.Base

record is-contr (A : Type) : Type where
  constructor _,_
  field
    centre  : A
    path-to : ∀ x → centre ≡ x

open is-contr public

is-prop : Type → Type
is-prop A = (x y : A) → x ≡ y

is-set : Type → Type
is-set A = (x y : A) (p q : x ≡ y) → Square p q refl refl

is-hlevel : Type → Nat → Type
is-hlevel A 0 = is-contr A
is-hlevel A 1 = is-prop  A
is-hlevel A (suc (suc n)) = (x y : A) → is-hlevel (x ≡ y) (suc n)

module _ where
  private variable
    A B : Type

  private
    _ : is-set A ≡ is-hlevel A 2
    _ = refl

  is-contr→is-prop : is-contr A → is-prop A
  is-contr→is-prop (a , path-a) x y = λ i →
    hcomp (λ { j (i = i0) → path-a x j
             ; j (i = i1) → path-a y j })
          a

  is-prop→is-set : is-prop A → is-set A
  is-prop→is-set path x y p q = λ i j →
    hcomp (λ { k (i = i0) → path x (p j) k
             ; k (i = i1) → path x (q j) k
             ; k (j = i0) → path x x     k
             ; k (j = i1) → path x y     k })
          x

  is-hlevel-suc : ∀ n → is-hlevel A n → is-hlevel A (suc n)
  is-hlevel-suc 0 = is-contr→is-prop
  is-hlevel-suc 1 = is-prop→is-set
  is-hlevel-suc (suc (suc n)) ncube x y = is-hlevel-suc (suc n) (ncube x y)

  is-hlevel-+ : ∀ n k → is-hlevel A n → is-hlevel A (k + n)
  is-hlevel-+ n zero = id
  is-hlevel-+ n (suc k) ncube = is-hlevel-suc (k + n) (is-hlevel-+ n k ncube)

  is-prop→is-hlevel-suc : ∀ n → is-prop A → is-hlevel A (suc n)
  is-prop→is-hlevel-suc zero = id
  is-prop→is-hlevel-suc (suc n) path = is-hlevel-suc (suc n) (is-prop→is-hlevel-suc n path)

  ⊤-is-contr : is-contr ⊤
  ⊤-is-contr = record
    { centre = tt
    ; path-to = λ { tt → refl }
    }

  ⊤-is-prop : is-prop ⊤
  ⊤-is-prop = λ tt tt → refl

  ⊤-is-hlevel : ∀ n → is-hlevel ⊤ n
  ⊤-is-hlevel zero = ⊤-is-contr
  ⊤-is-hlevel (suc n) = is-prop→is-hlevel-suc n ⊤-is-prop

  Path-is-hlevel : ∀ n → is-hlevel A (suc n) → ∀ x y → is-hlevel (Path A x y) n
  Path-is-hlevel 0 path x y = record
    { centre = path x y
    ; path-to = λ p → is-prop→is-set path x y (path x y) p
    }
  Path-is-hlevel (suc n) ncube x y = ncube x y

  PathP-is-hlevel : {A : 𝕀 → Type} (n : Nat) → is-hlevel (A i1) (suc n)
    → ∀ x y → is-hlevel (PathP A x y) n
  PathP-is-hlevel {A} n ncube x y =
    transport (λ A → is-hlevel A n) (sym (PathP≡Path0→1 A x y))
      $ Path-is-hlevel n ncube (coe0→1 A x) y

  is-prop∙→is-contr : A → is-prop A → is-contr A
  is-prop∙→is-contr a path = record
    { centre  = a
    ; path-to = λ x → path a x
    }

  is-contr-is-prop : is-prop (is-contr A)
  is-contr-is-prop (a₀ , path-a₀) (a₁ , path-a₁) = λ i → record
    { centre  = path-a₀ a₁ i
    ; path-to = λ x j →
        hcomp (λ { k (i = i0) → path-a₀ (path-a₀ x  j) k
                 ; k (i = i1) → path-a₀ (path-a₁ x  j) k
                 ; k (j = i0) → path-a₀ (path-a₀ a₁ i) k
                 ; k (j = i1) → path-a₀ x              k })
              a₀
    }

  is-prop-is-prop : is-prop (is-prop A)
  is-prop-is-prop path₀ path₁ = λ i x y →
    is-prop→is-set path₀ x y (path₀ x y) (path₁ x y) i

  is-set-is-prop : is-prop (is-set A)
  is-set-is-prop square₀ square₁ = λ i x y →
    is-prop-is-prop (square₀ x y) (square₁ x y) i

  is-hlevel-is-prop : ∀ n → is-prop (is-hlevel A n)
  is-hlevel-is-prop 0 = is-contr-is-prop
  is-hlevel-is-prop 1 = is-prop-is-prop
  is-hlevel-is-prop (suc (suc n)) ncube₀ ncube₁ = λ i x y →
    is-hlevel-is-prop (suc n) (ncube₀ x y) (ncube₁ x y) i

  is-prop→PathP : {A : 𝕀 → Type} → (∀ i → is-prop (A i))
    → ∀ a₀ a₁ → a₀ ≡ a₁ [ i ↦ A i ]
  is-prop→PathP {A} path a₀ a₁ = to-PathP $ path i1 (coe0→1 A a₀) a₁

  is-contr→extend : is-contr A → (φ : 𝔽) (u : Partial φ A) → A [ φ ↦ u ]
  is-contr→extend (a , path-a) φ u = inS do
    hcomp (λ { i (φ = i0) → a
             ; i (φ = i1) → path-a (u itIsOne) i })
          a

  extend→is-contr : ((φ : 𝔽) (u : Partial φ A) → A [ φ ↦ u ]) → is-contr A
  extend→is-contr extend = record
    { centre  =         outS (extend i0 λ ())
    ; path-to = λ x i → outS (extend i λ { (i = i1) → x })
    }

  retract→is-contr : (f : A → B) (g : B → A)
    → (∀ x → f (g x) ≡ x)
    → is-contr A
    → is-contr B
  retract→is-contr f g r (a , path-a) = record
    { centre = f a
    ; path-to = λ x → begin
        f   a  ≡⟨ cong f (path-a (g x)) ⟩
        f(g x) ≡⟨ r x ⟩
            x  ∎
    }

  retract→is-prop : (f : A → B) (g : B → A)
    → (∀ x → f (g x) ≡ x)
    → is-prop A
    → is-prop B
  retract→is-prop f g r path = λ a₀ a₁ i →
    hcomp (λ { j (i = i0) → r a₀ j
             ; j (i = i1) → r a₁ j })
          (f (path (g a₀) (g a₁) i))

  retract→is-set : (f : A → B) (g : B → A)
    → (∀ x → f (g x) ≡ x)
    → is-set A
    → is-set B
  retract→is-set f g r square = λ a₀ a₁ p q i j →
    hcomp (λ { k (i = i0) → r (p j) k
             ; k (i = i1) → r (q j) k
             ; k (j = i0) → r a₀    k
             ; k (j = i1) → r a₁    k })
          (f (square (g a₀) (g a₁) (cong g p) (cong g q) i j))

  retract→is-hlevel : ∀ n (f : A → B) (g : B → A)
    → (∀ x → f (g x) ≡ x)
    → is-hlevel A n
    → is-hlevel B n
  retract→is-hlevel 0 = retract→is-contr
  retract→is-hlevel 1 = retract→is-prop
  retract→is-hlevel (suc (suc n)) f g r ncube = λ a₀ a₁ →
    retract→is-hlevel (suc n)
      (λ ncube i → hcomp (λ { j (i = i0) → r a₀ j
                            ; j (i = i1) → r a₁ j })
                         (f (ncube i)))
      (cong g)
      (λ ncube i j → hcomp (λ { k (i = i1) → ncube j
                              ; k (j = i0) → r a₀ (i ∨ k)
                              ; k (j = i1) → r a₁ (i ∨ k) })
                           (r (ncube j) i))
      (ncube (g a₀) (g a₁))

  iso→is-hlevel : ∀ n → A ≅ B → is-hlevel A n → is-hlevel B n
  iso→is-hlevel n (fwd f) ncube =
    retract→is-hlevel n f (f ⁻¹) (λ x → cong (_$ x) (∘-invʳ f)) ncube

  iso→is-set : A ≅ B → is-set A → is-set B
  iso→is-set = iso→is-hlevel 2

  →‿is-contr : is-contr B → is-contr (A → B)
  →‿is-contr (b , path-b) = record
    { centre = λ _ → b
    ; path-to = λ f i x → path-b (f x) i
    }

  →‿is-prop : is-prop B → is-prop (A → B)
  →‿is-prop path = λ f g i x → path (f x) (g x) i

  →‿is-set : is-set B → is-set (A → B)
  →‿is-set square = λ f g p q i j x →
    square (f x) (g x) (cong (_$ x) p) (cong (_$ x) q) i j

  ×-is-contr : is-contr A → is-contr B → is-contr (A × B)
  ×-is-contr (a , path-a) (b , path-b) = record
    { centre = (a , b)
    ; path-to = λ (x , y) → cong₂ _,_ (path-a x) (path-b y)
    }

  ×-is-prop : is-prop A → is-prop B → is-prop (A × B)
  ×-is-prop pathA pathB = λ (a₀ , b₀) (a₁ , b₁) →
    cong₂ _,_ (pathA a₀ a₁) (pathB b₀ b₁)

  ×-is-set : is-set A → is-set B → is-set (A × B)
  ×-is-set squareA squareB = λ (a₀ , b₀) (a₁ , b₁) p q →
    cong₂ (cong₂ _,_)
      (squareA a₀ a₁ _ _)
      (squareB b₀ b₁ _ _)

  private variable
    x y : Σ A (const B)

  ×-Path-intro : (fst x ≡ fst y) × (snd x ≡ snd y) → x ≡ y
  ×-Path-intro (p , q) = λ i → (p i , q i)

  ×-Path-elim : x ≡ y → (fst x ≡ fst y) × (snd x ≡ snd y)
  ×-Path-elim p = (cong fst p , cong snd p)

  ×-Path-iso : ((fst x ≡ fst y) × (snd x ≡ snd y)) ≅ (x ≡ y)
  ×-Path-iso = record
    { fwd = ×-Path-intro
    ; iso = record
      { bwd = ×-Path-elim
      ; ∘-invˡ = refl
      ; ∘-invʳ = refl
      }
    }

  ×-is-hlevel : ∀ n → is-hlevel A n → is-hlevel B n → is-hlevel (A × B) n
  ×-is-hlevel 0 = ×-is-contr
  ×-is-hlevel 1 = ×-is-prop
  ×-is-hlevel (suc (suc n)) ncubeA ncubeB = λ (a₀ , b₀) (a₁ , b₁) →
    iso→is-hlevel (suc n) ×-Path-iso
      $ ×-is-hlevel (suc n) (ncubeA a₀ a₁) (ncubeB b₀ b₁)

module _ where
  private variable
    A : Type
    B : A → Type

  Π-is-contr : (∀ x → is-contr (B x)) → is-contr (∀ x → B x)
  Π-is-contr h = record
    { centre  = λ x → h x .centre
    ; path-to = λ f i x → h x .path-to (f x) i
    }

  Π-is-prop : (∀ x → is-prop (B x)) → is-prop (∀ x → B x)
  Π-is-prop path = λ f g i x → path x (f x) (g x) i

  Π-is-set : (∀ x → is-set (B x)) → is-set (∀ x → B x)
  Π-is-set square = λ f g p q i j x →
    square x (f x) (g x) (cong (_$ x) p) (cong (_$ x) q) i j

  private variable
    f g : ∀ x → B x

  Π-Path-intro : (∀ x → f x ≡ g x) → f ≡ g
  Π-Path-intro p i x = p x i

  Π-Path-elim : f ≡ g → (∀ x → f x ≡ g x)
  Π-Path-elim p x i = p i x

  Π-Path-iso : (∀ x → f x ≡ g x) ≅ (f ≡ g)
  Π-Path-iso = record
    { fwd = Π-Path-intro
    ; iso = record
      { bwd = Π-Path-elim
      ; ∘-invˡ = refl
      ; ∘-invʳ = refl
      }
    }

  Π-is-hlevel : ∀ n → (∀ x → is-hlevel (B x) n) → is-hlevel (∀ x → B x) n
  Π-is-hlevel 0 = Π-is-contr
  Π-is-hlevel 1 = Π-is-prop
  Π-is-hlevel (suc (suc n)) ncube = λ f g →
    iso→is-hlevel (suc n) Π-Path-iso
      $ Π-is-hlevel (suc n) λ x → ncube x (f x) (g x)

  →‿is-hlevel : ∀ {A B : Type} n → is-hlevel B n → is-hlevel (A → B) n
  →‿is-hlevel 0 = →‿is-contr
  →‿is-hlevel 1 = →‿is-prop
  →‿is-hlevel (suc (suc n)) ncube = λ f g →
    iso→is-hlevel (suc n) Π-Path-iso
      $ Π-is-hlevel (suc n) λ x → ncube (f x) (g x)

  Πᵢ-is-contr : (∀ {x} → is-contr (B x)) → is-contr (∀ {x} → B x)
  Πᵢ-is-contr h = record
    { centre  = λ {x} → h {x} .centre
    ; path-to = λ f i {x} → h {x} .path-to (f {x}) i
    }

  Πᵢ-is-prop : (∀ {x} → is-prop (B x)) → is-prop (∀ {x} → B x)
  Πᵢ-is-prop path = λ f g i {x} → path {x} (f {x}) (g {x}) i

  Πᵢ-is-set : (∀ {x} → is-set (B x)) → is-set (∀ {x} → B x)
  Πᵢ-is-set square = λ f g p q i j {x} →
    square {x} (f {x}) (g {x})
      (cong (λ - → - {x}) p)
      (cong (λ - → - {x}) q)
      i j

  Σ-is-contr : is-contr A → (∀ x → is-contr (B x)) → is-contr (Σ A B)
  Σ-is-contr {B = B} (a , path-a) h = record
    { centre  = a , h a .centre
    ; path-to = λ (x , y) i →
        ( path-a x i
        , h (path-a x i) .path-to (coe1→i (λ j → B (path-a x j)) i y) i)
    }

  Σ-is-prop : is-prop A → (∀ x → is-prop (B x)) → is-prop (Σ A B)
  Σ-is-prop pathA pathB = λ (a₀ , b₀) (a₁ , b₁) i →
    ( pathA a₀ a₁ i
    , is-prop→PathP (λ i → pathB (pathA a₀ a₁ i)) b₀ b₁ i
    )

  Σ-Path-intro : {x y : Σ A B}
    → Σ[ p ∈ fst x ≡ fst y ] (snd x ≡ snd y [ i ↦ B (p i) ])
    → x ≡ y
  Σ-Path-intro (p , q) = λ i → (p i , q i)

  Σ-Path-elim : {x y : Σ A B}
    → x ≡ y
    → Σ[ p ∈ fst x ≡ fst y ] (snd x ≡ snd y [ i ↦ B (p i) ])
  Σ-Path-elim p = (cong fst p , ap snd p)

  Σ-Path-iso : {x y : Σ A B}
    → (Σ[ p ∈ fst x ≡ fst y ] (snd x ≡ snd y [ i ↦ B (p i) ])) ≅ (x ≡ y)
  Σ-Path-iso = record
    { fwd = Σ-Path-intro
    ; iso = record
      { bwd = Σ-Path-elim
      ; ∘-invˡ = refl
      ; ∘-invʳ = refl
      }
    }

  Σ-is-hlevel : ∀ n → is-hlevel A n → (∀ x → is-hlevel (B x) n) → is-hlevel (Σ A B) n
  Σ-is-hlevel 0 = Σ-is-contr
  Σ-is-hlevel 1 = Σ-is-prop
  Σ-is-hlevel (suc (suc n)) ncubeA ncubeB (a₀ , b₀) (a₁ , b₁) =
    iso→is-hlevel (suc n) Σ-Path-iso
      $ Σ-is-hlevel (suc n)
          (ncubeA a₀ a₁)
          λ _ → PathP-is-hlevel (suc n) (ncubeB a₁) b₀ b₁

  Σ-is-set : is-set A → (∀ x → is-set (B x)) → is-set (Σ A B)
  Σ-is-set = Σ-is-hlevel 2

record _-Type (n : Nat) : Type where
  constructor _,_
  field
    ∣_∣ : Type
    hlevel : is-hlevel ∣_∣ n

open _-Type public using (∣_∣; hlevel)

rop = 1 -Type
Set  = 2 -Type

instance
  Set-underlying : Underlying Set
  Set-underlying = underlying-instance ∣_∣

module Automation where
  record IsHLevel (A : Type) n : Type where
    constructor hlevel-instance
    field
      hlevel : is-hlevel A n

  private variable
    A : Type
    B : A → Type

  hlevel! : ∀ n ⦃ _ : IsHLevel A n ⦄ → is-hlevel A n
  hlevel! n ⦃ hlevel-instance ncube ⦄ = ncube

  IsContr : (A : Type) → Type
  IsProp  : (A : Type) → Type
  IsSet   : (A : Type) → Type
  IsContr A = IsHLevel A 0
  IsProp  A = IsHLevel A 1
  IsSet   A = IsHLevel A 2

  instance
    ⊤-HLevel : ∀ {n}
      → IsHLevel ⊤ n
    ⊤-HLevel {n} = hlevel-instance $ ⊤-is-hlevel n

    Π-HLevel : ∀ {n}
      → ⦃ _ : ∀ {x} → IsHLevel (B x) n ⦄
      → IsHLevel (∀ x → B x) n
    Π-HLevel {n = n} = hlevel-instance $ Π-is-hlevel n λ _ → hlevel! n

    Σ-HLevel : ∀ {n}
      → ⦃ _ : IsHLevel A n ⦄
      → ⦃ _ : ∀ {x} → IsHLevel (B x) n ⦄
      → IsHLevel (Σ A B) n
    Σ-HLevel {n = n} = hlevel-instance $ Σ-is-hlevel n (hlevel! n) λ _ → hlevel! n

  el! : ∀ {n} (A : Type) ⦃ _ : IsHLevel A n ⦄ → n -Type
  el! {n} A = A , hlevel! n

open Automation public
