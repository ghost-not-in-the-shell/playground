module BigStepNormalization where
open import Data.List     hiding (map; lookup)
open import Data.List.All
open import Data.List.Any hiding (map)
open import Data.List.Membership.Propositional
open import Relation.Binary.PropositionalEquality

pattern ze = here refl
pattern su x = there x

infixr 5 _+_
infixr 6 _×_
infixr 7 _⇒_
data Ty : Set where
  𝟘 : Ty
  𝟙 : Ty
  𝟚 : Ty
  ℕ : Ty
  _+_ : Ty → Ty → Ty
  _×_ : Ty → Ty → Ty
  _⇒_ : Ty → Ty → Ty

Con = List Ty

data Tm (Γ : Con) : Ty → Set where
  absurd : ∀ {𝔸}
    → Tm Γ 𝟘
    → Tm Γ 𝔸

  sole : Tm Γ 𝟙

  true  : Tm Γ 𝟚
  false : Tm Γ 𝟚
  if    : ∀ {𝔸}
    → Tm Γ 𝟚
    → Tm Γ 𝔸
    → Tm Γ 𝔸
    → Tm Γ 𝔸

  zero : Tm Γ ℕ
  suc  : Tm Γ ℕ
       → Tm Γ ℕ
  rec : ∀ {𝔸}
    → Tm Γ ℕ
    → Tm Γ 𝔸
    → Tm Γ (ℕ ⇒ 𝔸 ⇒ 𝔸)
    → Tm Γ 𝔸

  inj₁ : ∀ {𝔸 𝔹}
    → Tm Γ 𝔸
    → Tm Γ (𝔸 + 𝔹)
  inj₂ : ∀ {𝔸 𝔹}
    → Tm Γ 𝔹
    → Tm Γ (𝔸 + 𝔹)
  case : ∀ {𝔸 𝔹 ℂ}
    → Tm Γ (𝔸 + 𝔹)
    → Tm Γ (𝔸 ⇒ ℂ)
    → Tm Γ (𝔹 ⇒ ℂ)
    → Tm Γ ℂ

  cons : ∀ {𝔸 𝔹}
    → Tm Γ 𝔸
    → Tm Γ 𝔹
    → Tm Γ (𝔸 × 𝔹)
  car : ∀ {𝔸 𝔹}
    → Tm Γ (𝔸 × 𝔹)
    → Tm Γ 𝔸
  cdr : ∀ {𝔸 𝔹}
    → Tm Γ (𝔸 × 𝔹)
    → Tm Γ 𝔹

  var : ∀ {𝔸}
    → 𝔸 ∈ Γ
    → Tm Γ 𝔸
  lam : ∀ {𝔸 𝔹}
    → Tm (𝔸 ∷ Γ) 𝔹
    → Tm Γ (𝔸 ⇒ 𝔹)
  app : ∀ {𝔸 𝔹}
    → Tm Γ (𝔸 ⇒ 𝔹)
    → Tm Γ 𝔸
    → Tm Γ 𝔹

data Ne (Nf : Con → Ty → Set) (Γ : Con) : Ty → Set where
  absurd : ∀ {𝔸}
    → Ne Nf Γ 𝟘
    → Ne Nf Γ 𝔸

  if : ∀ {𝔸}
    → Ne Nf Γ 𝟚
    → Nf    Γ 𝔸
    → Nf    Γ 𝔸
    → Ne Nf Γ 𝔸

  rec : ∀ {𝔸}
    → Ne Nf Γ ℕ
    → Nf    Γ 𝔸
    → Nf    Γ (ℕ ⇒ 𝔸 ⇒ 𝔸)
    → Ne Nf Γ 𝔸

  case : ∀ {𝔸 𝔹 ℂ}
    → Ne Nf Γ (𝔸 + 𝔹)
    → Nf    Γ (𝔸 ⇒ ℂ)
    → Nf    Γ (𝔹 ⇒ ℂ)
    → Ne Nf Γ ℂ

  car : ∀ {𝔸 𝔹}
    → Ne Nf Γ (𝔸 × 𝔹)
    → Ne Nf Γ 𝔸

  cdr : ∀ {𝔸 𝔹}
    → Ne Nf Γ (𝔸 × 𝔹)
    → Ne Nf Γ 𝔹

  var : ∀ {𝔸}
    → 𝔸 ∈ Γ
    → Ne Nf Γ 𝔸

  app : ∀ {𝔸 𝔹}
    → Ne Nf Γ (𝔸 ⇒ 𝔹)
    → Nf    Γ 𝔸
    → Ne Nf Γ 𝔹

mutual
  data Whnf (Δ : Con) : Ty → Set where
    ne : ∀ {𝔸}
      → Ne Whnf Δ 𝔸
      → Whnf    Δ 𝔸

    sole : Whnf Δ 𝟙

    true  : Whnf Δ 𝟚
    false : Whnf Δ 𝟚

    zero : Whnf Δ ℕ
    suc  : Whnf Δ ℕ
         → Whnf Δ ℕ

    inj₁ : ∀ {𝔸 𝔹}
      → Whnf Δ 𝔸
      → Whnf Δ (𝔸 + 𝔹)
    inj₂ : ∀ {𝔸 𝔹}
      → Whnf Δ 𝔹
      → Whnf Δ (𝔸 + 𝔹)

    cons : ∀ {𝔸 𝔹}
      → Whnf Δ 𝔸
      → Whnf Δ 𝔹
      → Whnf Δ (𝔸 × 𝔹)

    lam : ∀ {Γ 𝔸 𝔹}
      → Tm (𝔸 ∷ Γ) 𝔹
      → Sub  Δ Γ
      → Whnf Δ (𝔸 ⇒ 𝔹)

  Sub : Con → Con → Set
  Sub Δ Γ = All (Whnf Δ) Γ

mutual
  do-absurd : ∀ {Δ 𝔸} → Whnf Δ 𝟘 → Whnf Δ 𝔸
  do-absurd (ne ⁉) = ne (absurd ⁉)

  do-if : ∀ {Δ 𝔸} → Whnf Δ 𝟚 → Whnf Δ 𝔸 → Whnf Δ 𝔸 → Whnf Δ 𝔸
  do-if (ne b) t f = ne (if b t f)
  do-if true   t f = t
  do-if false  t f = f

  do-rec : ∀ {Δ 𝔸} → Whnf Δ ℕ → Whnf Δ 𝔸 → Whnf Δ (ℕ ⇒ 𝔸 ⇒ 𝔸) → Whnf Δ 𝔸
  do-rec (ne n)  z s = ne (rec n z s)
  do-rec zero    z s = z
  do-rec (suc n) z s = do-app (do-app s n) (do-rec n z s)

  do-case : ∀ {Δ 𝔸 𝔹 ℂ} → Whnf Δ (𝔸 + 𝔹) → Whnf Δ (𝔸 ⇒ ℂ) → Whnf Δ (𝔹 ⇒ ℂ) → Whnf Δ ℂ
  do-case (ne   s) l r = ne (case s l r)
  do-case (inj₁ a) l r = do-app l a
  do-case (inj₂ b) l r = do-app r b

  do-car : ∀ {Δ 𝔸 𝔹} → Whnf Δ (𝔸 × 𝔹) → Whnf Δ 𝔸
  do-car (ne   p)   = ne (car p)
  do-car (cons a b) = a

  do-cdr : ∀ {Δ 𝔸 𝔹} → Whnf Δ (𝔸 × 𝔹) → Whnf Δ 𝔹
  do-cdr (ne   p)   = ne (cdr p)
  do-cdr (cons a b) = b

  do-app : ∀ {Δ 𝔸 𝔹} → Whnf Δ (𝔸 ⇒ 𝔹) → Whnf Δ 𝔸 → Whnf Δ 𝔹
  do-app (ne  t)   u = ne (app t u)
  do-app (lam t ρ) u = eval t (u ∷ ρ)

  {-# TERMINATING #-}
  eval : ∀ {Γ Δ 𝔸} → Tm Γ 𝔸 → Sub Δ Γ → Whnf Δ 𝔸
  eval (absurd ⁉)   ρ = do-absurd (eval ⁉ ρ)
  eval sole         ρ = sole
  eval true         ρ = true
  eval false        ρ = false
  eval (if b t f)   ρ = do-if (eval b ρ) (eval t ρ) (eval f ρ)
  eval zero         ρ = zero
  eval (suc n)      ρ = suc (eval n ρ)
  eval (rec n z s)  ρ = do-rec (eval n ρ) (eval z ρ) (eval s ρ)
  eval (inj₁ a)     ρ = inj₁ (eval a ρ)
  eval (inj₂ b)     ρ = inj₂ (eval b ρ)
  eval (case s l r) ρ = do-case (eval s ρ) (eval l ρ) (eval r ρ)
  eval (cons a b)   ρ = cons (eval a ρ) (eval b ρ)
  eval (car p)      ρ = do-car (eval p ρ)
  eval (cdr p)      ρ = do-cdr (eval p ρ)
  eval (var x)      ρ = lookup ρ x
  eval (lam t)      ρ = lam t ρ
  eval (app t u)    ρ = do-app (eval t ρ) (eval u ρ)

data Nf (Γ : Con) : Ty → Set where
  ne : ∀ {𝔸}
    → Ne Nf Γ 𝔸
    → Nf    Γ 𝔸

  sole : Nf Γ 𝟙

  true  : Nf Γ 𝟚
  false : Nf Γ 𝟚

  zero : Nf Γ ℕ
  suc  : Nf Γ ℕ
       → Nf Γ ℕ

  inj₁ : ∀ {𝔸 𝔹}
    → Nf Γ 𝔸
    → Nf Γ (𝔸 + 𝔹)
  inj₂ : ∀ {𝔸 𝔹}
    → Nf Γ 𝔹
    → Nf Γ (𝔸 + 𝔹)

  cons : ∀ {𝔸 𝔹}
    → Nf Γ 𝔸
    → Nf Γ 𝔹
    → Nf Γ (𝔸 × 𝔹)

  lam : ∀ {𝔸 𝔹}
    → Nf (𝔸 ∷ Γ) 𝔹
    → Nf Γ (𝔸 ⇒ 𝔹)

data OPE : Con → Con → Set where
  done : OPE [] []
  skip : ∀ {Δ Γ 𝔸} → OPE Δ Γ → OPE (𝔸 ∷ Δ)      Γ
  keep : ∀ {Δ Γ 𝔸} → OPE Δ Γ → OPE (𝔸 ∷ Δ) (𝔸 ∷ Γ)

id : ∀ {Γ} → OPE Γ Γ
id {[]}    = done
id {_ ∷ _} = keep id

_∘_ : ∀ {Ε Δ Γ} → OPE Δ Γ → OPE Ε Δ → OPE Ε Γ
w₁      ∘ done    = w₁
w₁      ∘ skip w₂ = skip (w₁ ∘ w₂)
skip w₁ ∘ keep w₂ = skip (w₁ ∘ w₂)
keep w₁ ∘ keep w₂ = keep (w₁ ∘ w₂)

↑ : ∀ {Γ 𝔸} → OPE (𝔸 ∷ Γ) Γ
↑ = skip id

rename∋ : ∀ {Δ Γ} → OPE Δ Γ → ∀ {𝔸} → 𝔸 ∈ Γ → 𝔸 ∈ Δ
rename∋ done ()
rename∋ (skip w) x      = su (rename∋ w x)
rename∋ (keep w) ze     = ze
rename∋ (keep w) (su x) = su (rename∋ w x)

renameᵀᵐ : ∀ {Δ Γ} → OPE Δ Γ → ∀ {𝔸} → Tm Γ 𝔸 → Tm Δ 𝔸
renameᵀᵐ w (absurd ⁉)   = absurd (renameᵀᵐ w ⁉)
renameᵀᵐ w sole         = sole
renameᵀᵐ w true         = true
renameᵀᵐ w false        = false
renameᵀᵐ w (if b t f)   = if (renameᵀᵐ w b) (renameᵀᵐ w t) (renameᵀᵐ w f)
renameᵀᵐ w zero         = zero
renameᵀᵐ w (suc n)      = suc (renameᵀᵐ w n)
renameᵀᵐ w (rec n z s)  = rec (renameᵀᵐ w n) (renameᵀᵐ w z) (renameᵀᵐ w s)
renameᵀᵐ w (inj₁ a)     = inj₁ (renameᵀᵐ w a)
renameᵀᵐ w (inj₂ b)     = inj₂ (renameᵀᵐ w b)
renameᵀᵐ w (case s l r) = case (renameᵀᵐ w s) (renameᵀᵐ w l) (renameᵀᵐ w r)
renameᵀᵐ w (cons a b)   = cons (renameᵀᵐ w a) (renameᵀᵐ w b)
renameᵀᵐ w (car p)      = car (renameᵀᵐ w p)
renameᵀᵐ w (cdr p)      = cdr (renameᵀᵐ w p)
renameᵀᵐ w (var x)      = var (rename∋ w x)
renameᵀᵐ w (lam t)      = lam (renameᵀᵐ (keep w) t)
renameᵀᵐ w (app t u)    = app (renameᵀᵐ w t) (renameᵀᵐ w u)

module _ {Nf : Con → Ty → Set}
         (renameᴺᶠ : ∀ {Δ Γ} → OPE Δ Γ → ∀ {𝔸} → Nf Γ 𝔸 → Nf Δ 𝔸) where
  renameᴺᵉ : ∀ {Δ Γ} → OPE Δ Γ → ∀ {𝔸} → Ne Nf Γ 𝔸 → Ne Nf Δ 𝔸
  renameᴺᵉ w (absurd ⁉)   = absurd (renameᴺᵉ w ⁉)
  renameᴺᵉ w (if b t f)   = if     (renameᴺᵉ w b) (renameᴺᶠ w t) (renameᴺᶠ w f)
  renameᴺᵉ w (rec  n z s) = rec    (renameᴺᵉ w n) (renameᴺᶠ w z) (renameᴺᶠ w s)
  renameᴺᵉ w (case s l r) = case   (renameᴺᵉ w s) (renameᴺᶠ w l) (renameᴺᶠ w r)
  renameᴺᵉ w (car p)      = car    (renameᴺᵉ w p)
  renameᴺᵉ w (cdr p)      = cdr    (renameᴺᵉ w p)
  renameᴺᵉ w (var x)      = var    (rename∋  w x)
  renameᴺᵉ w (app t u)    = app    (renameᴺᵉ w t) (renameᴺᶠ w u)

mutual
  {-# TERMINATING #-}
  renameᵂʰⁿᶠ : ∀ {Δ Γ} → OPE Δ Γ → ∀ {𝔸} → Whnf Γ 𝔸 → Whnf Δ 𝔸
  renameᵂʰⁿᶠ w (ne t)     = ne (renameᴺᵉ renameᵂʰⁿᶠ w t)
  renameᵂʰⁿᶠ w sole       = sole
  renameᵂʰⁿᶠ w true       = true
  renameᵂʰⁿᶠ w false      = false
  renameᵂʰⁿᶠ w zero       = zero
  renameᵂʰⁿᶠ w (suc n)    = suc (renameᵂʰⁿᶠ w n)
  renameᵂʰⁿᶠ w (inj₁ a)   = inj₁ (renameᵂʰⁿᶠ w a)
  renameᵂʰⁿᶠ w (inj₂ b)   = inj₂ (renameᵂʰⁿᶠ w b)
  renameᵂʰⁿᶠ w (cons a b) = cons (renameᵂʰⁿᶠ w a) (renameᵂʰⁿᶠ w b)
  renameᵂʰⁿᶠ w (lam t ρ)  = lam t (renameᴱⁿᵛ w ρ)

  renameᴱⁿᵛ : ∀ {Δ Γ} → OPE Δ Γ → ∀ {𝔸⃗} → Sub Γ 𝔸⃗ → Sub Δ 𝔸⃗
  renameᴱⁿᵛ w = map (renameᵂʰⁿᶠ w)

{-# TERMINATING #-}
renameᴺᶠ : ∀ {Δ Γ} → OPE Δ Γ → ∀ {𝔸} → Nf Γ 𝔸 → Nf Δ 𝔸
renameᴺᶠ w (ne t)     = ne (renameᴺᵉ renameᴺᶠ w t)
renameᴺᶠ w sole       = sole
renameᴺᶠ w true       = true
renameᴺᶠ w false      = false
renameᴺᶠ w zero       = zero
renameᴺᶠ w (suc n)    = suc (renameᴺᶠ w n)
renameᴺᶠ w (inj₁ a)   = inj₁ (renameᴺᶠ w a)
renameᴺᶠ w (inj₂ b)   = inj₂ (renameᴺᶠ w b)
renameᴺᶠ w (cons a b) = cons (renameᴺᶠ w a) (renameᴺᶠ w b)
renameᴺᶠ w (lam t)    = lam (renameᴺᶠ (keep w) t)

mutual
  quoteᴺᵉ : ∀ {𝔸 Γ} → Ne Whnf Γ 𝔸 → Ne Nf Γ 𝔸
  quoteᴺᵉ (absurd ⁉)   = absurd (quoteᴺᵉ ⁉)
  quoteᴺᵉ (if   b t f) = if   (quoteᴺᵉ b) (quoteᴺᶠ t) (quoteᴺᶠ f)
  quoteᴺᵉ (rec  n z s) = rec  (quoteᴺᵉ n) (quoteᴺᶠ z) (quoteᴺᶠ s)
  quoteᴺᵉ (case s l r) = case (quoteᴺᵉ s) (quoteᴺᶠ l) (quoteᴺᶠ r)
  quoteᴺᵉ (car p)      = car (quoteᴺᵉ p)
  quoteᴺᵉ (cdr p)      = cdr (quoteᴺᵉ p)
  quoteᴺᵉ (var x)      = var x
  quoteᴺᵉ (app t u)    = app (quoteᴺᵉ t) (quoteᴺᶠ u)

  {-# TERMINATING #-}
  quoteᴺᶠ : ∀ {𝔸 Γ} → Whnf Γ 𝔸 → Nf Γ 𝔸
  quoteᴺᶠ {𝟘}     (ne   ⁉)   = ne   (quoteᴺᵉ ⁉)
  quoteᴺᶠ {𝟙}     _          = sole
  quoteᴺᶠ {𝟚}     (ne   b)   = ne   (quoteᴺᵉ b)
  quoteᴺᶠ {𝟚}     true       = true
  quoteᴺᶠ {𝟚}     false      = false
  quoteᴺᶠ {ℕ}     (ne   n)   = ne   (quoteᴺᵉ n)
  quoteᴺᶠ {ℕ}     zero       = zero
  quoteᴺᶠ {ℕ}     (suc  n)   = suc  (quoteᴺᶠ n)
  quoteᴺᶠ {𝔸 + 𝔹} (ne   s)   = ne   (quoteᴺᵉ s)
  quoteᴺᶠ {𝔸 + 𝔹} (inj₁ a)   = inj₁ (quoteᴺᶠ a)
  quoteᴺᶠ {𝔸 + 𝔹} (inj₂ b)   = inj₂ (quoteᴺᶠ b)
  quoteᴺᶠ {𝔸 × 𝔹} p          = cons (quoteᴺᶠ (do-car p)) (quoteᴺᶠ (do-cdr p))
  quoteᴺᶠ {𝔸 ⇒ 𝔹} t          = lam  (quoteᴺᶠ (do-app (renameᵂʰⁿᶠ ↑ t) (ne (var ze))))

idᴱⁿᵛ : ∀ {Γ} → Sub Γ Γ
idᴱⁿᵛ {[]}    = []
idᴱⁿᵛ {_ ∷ _} = ne (var ze) ∷ renameᴱⁿᵛ ↑ idᴱⁿᵛ

nf : ∀ {Γ 𝔸} → Tm Γ 𝔸 → Nf Γ 𝔸
nf t = quoteᴺᶠ (eval t idᴱⁿᵛ)
