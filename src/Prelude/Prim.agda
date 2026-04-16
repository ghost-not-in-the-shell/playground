module Prelude.Prim where

private module Universe where
{-# BUILTIN TYPE             Type  #-}
{-# BUILTIN SETOMEGA         Typeω #-}
{-# BUILTIN PROP             Prop  #-}
{-# BUILTIN PROPOMEGA        Propω #-}
{-# BUILTIN STRICTSET        SSet  #-}
{-# BUILTIN STRICTSETOMEGA   SSetω #-}
{-# BUILTIN LEVELUNIV        ℓUniv #-}
{-# BUILTIN CUBEINTERVALUNIV 𝕀Univ #-}

postulate
  Level : ℓUniv
  lzero : Level
  lsuc  : Level → Level
  _⊔_   : Level → Level → Level

infixl 6 _⊔_

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC  lsuc  #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

open Universe public

private module Interval where
  {-# BUILTIN INTERVAL 𝕀  #-}
  {-# BUILTIN IZERO    i0 #-}
  {-# BUILTIN IONE     i1 #-}

  primitive
    primIMin : 𝕀 → 𝕀 → 𝕀
    primIMax : 𝕀 → 𝕀 → 𝕀
    primINeg : 𝕀 → 𝕀

  infix  30 primINeg
  infixr 20 primIMin primIMax

open Interval public
  renaming ( primIMin to _∧_
           ; primIMax to _∨_
           ; primINeg to ~_ )

private module Partial where
  𝔽 : 𝕀Univ
  𝔽 = 𝕀

  infix 4 _=i1
  {-# BUILTIN ISONE _=i1 #-} -- _=i1 : 𝔽 → SSet

  postulate
    always : i1 =i1
    left   : (φ ψ : 𝔽) → φ =i1 → φ ∨ ψ =i1
    right  : (φ ψ : 𝔽) → ψ =i1 → φ ∨ ψ =i1

  {-# BUILTIN ITISONE always #-}
  {-# BUILTIN ISONE1  left   #-}
  {-# BUILTIN ISONE2  right  #-}

  {-# BUILTIN PARTIAL  Partial  #-}
  {-# BUILTIN PARTIALP PartialP #-}

  primitive
    primPOr : ∀ {ℓ} (φ ψ : 𝔽) {A : Partial (φ ∨ ψ) (Type ℓ)}
      → (u : PartialP φ (λ φ=i1 → A (left  φ ψ φ=i1)))
      → (v : PartialP ψ (λ ψ=i1 → A (right φ ψ ψ=i1)))
      → PartialP (φ ∨ ψ) A

  syntax primPOr φ ψ u v = [ φ ↦ u , ψ ↦ v ]

  {-# BUILTIN SUB Sub #-}

  infix 4 _[_↦_]
  _[_↦_] : ∀ {ℓ} (A : Type ℓ) (φ : 𝔽) (u : Partial φ A) → SSet ℓ
  _[_↦_] = Sub

  postulate
    inS : ∀ {ℓ} {A : Type ℓ} {φ : 𝔽}
      → (a : A) → A [ φ ↦ (λ {(φ = i1) → a}) ]

  {-# BUILTIN SUBIN inS #-}

  primitive
    primSubOut : ∀ {ℓ} {A : Type ℓ} {φ : 𝔽} {u : Partial φ A}
      → A [ φ ↦ u ] → A

open Partial public
  renaming ( primSubOut to outS )

private module Kan where
  primitive
    primTransp : ∀ {ℓ} (A : ∀ i → Type (ℓ i)) (φ : 𝔽) (a : A i0) → A i1
    primHComp  : ∀ {ℓ} {A :       Type  ℓ   } {φ : 𝔽} (u : ∀ i → Partial φ  A   ) (a : A   ) → A
    primComp   : ∀ {ℓ} (A : ∀ i → Type (ℓ i)) {φ : 𝔽} (u : ∀ i → Partial φ (A i)) (a : A i0) → A i1

  hfill : ∀ {ℓ} {A : Type ℓ} {φ : 𝔽}
    → (u  : ∀ i → Partial φ A)
    → (u₀ : A [ φ ↦ u i0 ])
    → (i : 𝕀) → A
  hfill {φ = φ} u u₀ = λ i →
    primHComp (λ { j (φ = i1) → u (i ∧ j) always
                 ; j (i = i0) → outS u₀ })
              (outS u₀)

  fill : {ℓ : 𝕀 → Level} (A : ∀ i → Type (ℓ i)) {φ : 𝔽}
    → (u  : ∀ i → Partial φ (A i))
    → (u₀ : A i0 [ φ ↦ u i0 ])
    → (i : 𝕀) → A i
  fill A {φ} u u₀ = λ i →
    primComp (λ j → A (i ∧ j))
             (λ { j (φ = i1) → u (i ∧ j) always
                ; j (i = i0) → outS u₀ })
             (outS u₀)

open Kan public
  renaming ( primTransp to transp
           ; primHComp  to hcomp
           ; primComp   to comp )

private module Path where
  postulate
    PathP : ∀ {ℓ} (A : 𝕀 → Type ℓ) → A i0 → A i1 → Type ℓ

  {-# BUILTIN PATHP PathP #-}

  infix 4 PathP
  syntax PathP (λ i → A) x y = x ≡ y [ i ↦ A ]

  Path : ∀ {ℓ} (A : Type ℓ) → A → A → Type ℓ
  Path A x y = PathP (λ i → A) x y

  infix 4 _≡_
  _≡_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ
  x ≡ y = Path _ x y

  {-# BUILTIN PATH _≡_ #-}

open Path public

private module Data where
  data ⊥ : Type where

  record ⊤ : Type where
    constructor tt

  {-# BUILTIN UNIT ⊤ #-}

  data Bool : Type where
    false true : Bool

  data Nat : Type where
    zero : Nat
    suc  : Nat → Nat

  {-# BUILTIN NATURAL Nat #-}

  infixl 5 _+_
  _+_ : Nat → Nat → Nat
  zero  + n = n
  suc m + n = suc (m + n)

  infixr 4 _,_
  record Σ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : A → Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
    constructor _,_
    field
      fst : A
      snd : B fst

  open Σ public

  {-# BUILTIN SIGMA Σ #-}

  infix 4 -,
  pattern -, b = _ , b

  infix 2 Σ-syntax
  Σ-syntax : ∀ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : A → Type ℓ₂) → Type (ℓ₁ ⊔ ℓ₂)
  Σ-syntax = Σ
  syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

open Data public

module Misc where
  const : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂}
    → (x : A) → B x → A
  const x = λ _ → x

  flip : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : A → B → Type ℓ₃}
    → (∀ x y → C x y) → (∀ y x → C x y)
  flip f = λ y x → f x y

  infixr -1 _$_
  _$_ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂}
    → (∀ x → B x) → (∀ x → B x)
  f $ x = f x

open Misc public

postulate
  🚧 : ∀ {ℓ} {A : Type ℓ} → A
