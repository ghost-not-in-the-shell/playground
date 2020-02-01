open import Data.List using (List; []; _∷_)
open import Data.List.All using (All; []; _∷_; lookup)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (refl)

pattern ze   = here refl
pattern su x = there x

data Ty : Set where
  𝟙   : Ty
  𝟘   : Ty
  _∧_ : Ty → Ty → Ty
  _∨_ : Ty → Ty → Ty
  _⇒_ : Ty → Ty → Ty

infixr 7 _∧_
infixr 6 _∨_
infixl 5 _⇒_

Con = List Ty

data Tm (Γ : Con) : Ty → Set where
  var : ∀ {𝔸} → 𝔸 ∈ Γ → Tm Γ 𝔸

  sole : Tm Γ 𝟙

  cons : ∀ {𝔸 𝔹} → Tm Γ 𝔸 → Tm Γ 𝔹 → Tm Γ (𝔸 ∧ 𝔹)
  car  : ∀ {𝔸 𝔹} → Tm Γ (𝔸 ∧ 𝔹) → Tm Γ 𝔸
  cdr  : ∀ {𝔸 𝔹} → Tm Γ (𝔸 ∧ 𝔹) → Tm Γ 𝔹

  lam : ∀ {𝔸 𝔹} → Tm (𝔸 ∷ Γ) 𝔹 → Tm Γ (𝔸 ⇒ 𝔹)
  app : ∀ {𝔸 𝔹} → Tm Γ (𝔸 ⇒ 𝔹) → Tm Γ 𝔸 → Tm Γ 𝔹

  absurd : ∀ {ℂ} → Tm Γ 𝟘 → Tm Γ ℂ

  left  : ∀ {𝔸 𝔹} → Tm Γ 𝔸 → Tm Γ (𝔸 ∨ 𝔹)
  right : ∀ {𝔸 𝔹} → Tm Γ 𝔹 → Tm Γ (𝔸 ∨ 𝔹)
  case  : ∀ {𝔸 𝔹 ℂ} → Tm Γ (𝔸 ∨ 𝔹) → Tm (𝔸 ∷ Γ) ℂ → Tm (𝔹 ∷ Γ) ℂ → Tm Γ ℂ

mutual
  data Nf (Γ : Con) : Ty → Set where
    sole  : Nf Γ 𝟙
    lam   : ∀ {𝔸 𝔹} → Nf (𝔸 ∷ Γ) 𝔹 → Nf Γ (𝔸 ⇒ 𝔹)
    cons  : ∀ {𝔸 𝔹} → Nf Γ 𝔸 → Nf Γ 𝔹 → Nf Γ (𝔸 ∧ 𝔹)
    left  : ∀ {𝔸 𝔹} → Nf Γ 𝔸 → Nf Γ (𝔸 ∨ 𝔹)
    right : ∀ {𝔸 𝔹} → Nf Γ 𝔹 → Nf Γ (𝔸 ∨ 𝔹)
    ne    : ∀ {𝔸 ℂ} → 𝔸 ∈ Γ → Sp Γ 𝔸 ℂ → Nf Γ ℂ

  data Sp (Γ : Con) : Ty → Ty → Set where
    []          : ∀ {𝔸} → Sp Γ 𝔸 𝔸
    _∷_         : ∀ {𝔸 𝔹 ℂ} → Elim Γ 𝔸 𝔹 → Sp Γ 𝔹 ℂ → Sp Γ 𝔸 ℂ

  data Elim (Γ : Con) : Ty → Ty → Set where
    app₍-,_₎    : ∀ {𝔸 𝔹} → Nf Γ 𝔸 → Elim Γ (𝔸 ⇒ 𝔹) 𝔹
    car₍-₎      : ∀ {𝔸 𝔹} → Elim Γ (𝔸 ∧ 𝔹) 𝔸
    cdr₍-₎      : ∀ {𝔸 𝔹} → Elim Γ (𝔸 ∧ 𝔹) 𝔹
    absurd₍-₎   : ∀ {ℂ} → Elim Γ 𝟘 ℂ
    case₍-,_,_₎ : ∀ {𝔸 𝔹 ℂ} → Nf (𝔸 ∷ Γ) ℂ → Nf (𝔹 ∷ Γ) ℂ → Elim Γ (𝔸 ∨ 𝔹) ℂ

pattern var! x = ne x []

[_] : ∀ {Γ 𝔸 𝔹} → Elim Γ 𝔸 𝔹 → Sp Γ 𝔸 𝔹
[ e ] = e ∷ []

_++_ : ∀ {Γ 𝔸 𝔹 ℂ} → Sp Γ 𝔸 𝔹 → Sp Γ 𝔹 ℂ → Sp Γ 𝔸 ℂ
[]        ++ sp₂ = sp₂
(e ∷ sp₁) ++ sp₂ = e ∷ (sp₁ ++ sp₂)

data Ren : Con → Con → Set where
  done : Ren [] []
  skip : ∀ {Γ Δ 𝔸} → Ren Γ Δ → Ren (𝔸 ∷ Γ) Δ
  keep : ∀ {Γ Δ 𝔸} → Ren Γ Δ → Ren (𝔸 ∷ Γ) (𝔸 ∷ Δ)

id : ∀ {Γ} → Ren Γ Γ
id {[]   } = done
id {_ ∷ _} = keep id

_∘_ : ∀ {Γ Δ Ξ} → Ren Δ Ξ → Ren Γ Δ → Ren Γ Ξ
w₁      ∘ done    = w₁
w₁      ∘ skip w₂ = skip (w₁ ∘ w₂)
skip w₁ ∘ keep w₂ = skip (w₁ ∘ w₂)
keep w₁ ∘ keep w₂ = keep (w₁ ∘ w₂)

renᵛᵃʳ : ∀ {Γ Δ 𝔸} → Ren Γ Δ → 𝔸 ∈ Δ → 𝔸 ∈ Γ
renᵛᵃʳ (skip w) x      = su (renᵛᵃʳ w x)
renᵛᵃʳ (keep w) ze     = ze
renᵛᵃʳ (keep w) (su x) = su (renᵛᵃʳ w x)

renᵗᵐ : ∀ {Γ Δ 𝔸} → Ren Γ Δ → Tm Δ 𝔸 → Tm Γ 𝔸
renᵗᵐ w (var    x    ) = var    (renᵛᵃʳ      w  x)
renᵗᵐ w (sole        ) = sole
renᵗᵐ w (cons   t u  ) = cons   (renᵗᵐ       w  t) (renᵗᵐ       w  u)
renᵗᵐ w (car    t    ) = car    (renᵗᵐ       w  t)
renᵗᵐ w (cdr    t    ) = cdr    (renᵗᵐ       w  t)
renᵗᵐ w (lam    t    ) = lam    (renᵗᵐ (keep w) t)
renᵗᵐ w (app    t u  ) = app    (renᵗᵐ       w  t) (renᵗᵐ       w  u)
renᵗᵐ w (absurd t    ) = absurd (renᵗᵐ       w  t)
renᵗᵐ w (left   t    ) = left   (renᵗᵐ       w  t)
renᵗᵐ w (right  t    ) = right  (renᵗᵐ       w  t)
renᵗᵐ w (case   t u v) = case   (renᵗᵐ       w  t) (renᵗᵐ (keep w) u) (renᵗᵐ (keep w) v)

mutual
  renⁿᶠ : ∀ {Γ Δ 𝔸} → Ren Γ Δ → Nf Δ 𝔸 → Nf Γ 𝔸
  renⁿᶠ w (sole      ) = sole
  renⁿᶠ w (lam   t   ) = lam   (renⁿᶠ (keep w) t)
  renⁿᶠ w (cons  t u ) = cons  (renⁿᶠ       w  t) (renⁿᶠ w u)
  renⁿᶠ w (left  t   ) = left  (renⁿᶠ       w  t)
  renⁿᶠ w (right t   ) = right (renⁿᶠ       w  t)
  renⁿᶠ w (ne    x sp) = ne    (renᵛᵃʳ      w  x) (renˢᵖ w sp)

  renˢᵖ : ∀ {Γ Δ 𝔸 𝔹} → Ren Γ Δ → Sp Δ 𝔸 𝔹 → Sp Γ 𝔸 𝔹
  renˢᵖ w []       = []
  renˢᵖ w (e ∷ sp) = renᵉˡⁱᵐ w e ∷ renˢᵖ w sp

  renᵉˡⁱᵐ : ∀ {Γ Δ 𝔸 𝔹} → Ren Γ Δ → Elim Δ 𝔸 𝔹 → Elim Γ 𝔸 𝔹
  renᵉˡⁱᵐ w app₍-, u ₎      = app₍-, renⁿᶠ w u ₎
  renᵉˡⁱᵐ w car₍-₎          = car₍-₎
  renᵉˡⁱᵐ w cdr₍-₎          = cdr₍-₎
  renᵉˡⁱᵐ w absurd₍-₎       = absurd₍-₎
  renᵉˡⁱᵐ w case₍-, u , v ₎ = case₍-, renⁿᶠ (keep w) u , renⁿᶠ (keep w) v ₎

Sub : Con → Con → Set
Sub Γ = All (Nf Γ)

_◐_ : ∀ {Γ Δ Ξ} → Sub Δ Ξ → Ren Γ Δ → Sub Γ Ξ
[]      ◐ w = []
(t ∷ ρ) ◐ w = renⁿᶠ w t ∷ (ρ ◐ w)

_◑_ : ∀ {Γ Δ Ξ} → Ren Δ Ξ → Sub Γ Δ → Sub Γ Ξ
done   ◑ []      = []
skip w ◑ (t ∷ ρ) =      w ◑ ρ
keep w ◑ (t ∷ ρ) = t ∷ (w ◑ ρ)

⌜done⌝ : Sub [] []
⌜skip⌝ : ∀ {Γ Δ 𝔸} → Sub Γ Δ → Sub (𝔸 ∷ Γ) Δ
⌜keep⌝ : ∀ {Γ Δ 𝔸} → Sub Γ Δ → Sub (𝔸 ∷ Γ) (𝔸 ∷ Δ)
⌜done⌝   = []
⌜skip⌝ ρ = ρ ◐ skip id
⌜keep⌝ ρ = var! ze ∷ ⌜skip⌝ ρ

⌜_⌝ : ∀ {Γ Δ} → Ren Γ Δ → Sub Γ Δ
⌜ done   ⌝ = ⌜done⌝
⌜ skip w ⌝ = ⌜skip⌝ ⌜ w ⌝
⌜ keep w ⌝ = ⌜keep⌝ ⌜ w ⌝

car! : ∀ {Γ 𝔸 𝔹} → Nf Γ (𝔸 ∧ 𝔹) → Nf Γ 𝔸
car! (cons t  u ) = t
car! (ne   x  sp) = ne x (sp ++ [ car₍-₎ ])

cdr! : ∀ {Γ 𝔸 𝔹} → Nf Γ (𝔸 ∧ 𝔹) → Nf Γ 𝔹
cdr! (cons t  u ) = u
cdr! (ne   x  sp) = ne x (sp ++ [ cdr₍-₎ ])

absurd! : ∀ {Γ ℂ} → Nf Γ 𝟘 → Nf Γ ℂ
absurd! (ne x sp) = ne x (sp ++ [ absurd₍-₎ ])

mutual
  app! : ∀ {Γ 𝔸 𝔹} → Nf Γ (𝔸 ⇒ 𝔹) → Nf Γ 𝔸 → Nf Γ 𝔹
  app! (lam t   ) u = subⁿᶠ (u ∷ ⌜ id  ⌝) t
  app! (ne  x sp) u = ne x (sp ++ [ app₍-, u ₎ ])

  case! : ∀ {Γ 𝔸 𝔹 ℂ} → Nf Γ (𝔸 ∨ 𝔹) → Nf (𝔸 ∷ Γ) ℂ → Nf (𝔹 ∷ Γ) ℂ → Nf Γ ℂ
  case! (left  t   ) u v = subⁿᶠ (t ∷ ⌜ id ⌝) u
  case! (right t   ) u v = subⁿᶠ (t ∷ ⌜ id ⌝) v
  case! (ne    x sp) u v = ne x (sp ++ [ case₍-, u , v ₎ ])

  {-# TERMINATING #-}
  subⁿᶠ : ∀ {Γ Δ 𝔸} → Sub Γ Δ → Nf Δ 𝔸 → Nf Γ 𝔸
  subⁿᶠ ρ (sole      ) = sole
  subⁿᶠ ρ (lam   t   ) = lam   (subⁿᶠ (⌜keep⌝ ρ) t)
  subⁿᶠ ρ (cons  t u ) = cons  (subⁿᶠ ρ t) (subⁿᶠ ρ u )
  subⁿᶠ ρ (left  t   ) = left  (subⁿᶠ ρ t)
  subⁿᶠ ρ (right t   ) = right (subⁿᶠ ρ t)
  subⁿᶠ ρ (ne    x sp) = elim (lookup ρ x) (subˢᵖ ρ sp)

  subˢᵖ : ∀ {Γ Δ 𝔸 𝔹} → Sub Γ Δ → Sp Δ 𝔸 𝔹 → Sp Γ 𝔸 𝔹
  subˢᵖ ρ []       = []
  subˢᵖ ρ (e ∷ sp) = subᵉˡⁱᵐ ρ e ∷ subˢᵖ ρ sp

  subᵉˡⁱᵐ : ∀ {Γ Δ 𝔸 𝔹} → Sub Γ Δ → Elim Δ 𝔸 𝔹 → Elim Γ 𝔸 𝔹
  subᵉˡⁱᵐ ρ app₍-, u ₎      = app₍-, subⁿᶠ ρ u ₎
  subᵉˡⁱᵐ ρ car₍-₎          = car₍-₎
  subᵉˡⁱᵐ ρ cdr₍-₎          = cdr₍-₎
  subᵉˡⁱᵐ ρ absurd₍-₎       = absurd₍-₎
  subᵉˡⁱᵐ ρ case₍-, u , v ₎ = case₍-, subⁿᶠ (⌜keep⌝ ρ) u , subⁿᶠ (⌜keep⌝ ρ) v ₎

  elim : ∀ {Γ 𝔸 𝔹} → Nf Γ 𝔸 → Sp Γ 𝔸 𝔹 → Nf Γ 𝔹
  elim t []                     = t
  elim t (app₍-, u ₎      ∷ sp) = elim (app!    t u  ) sp
  elim t (car₍-₎          ∷ sp) = elim (car!    t    ) sp
  elim t (cdr₍-₎          ∷ sp) = elim (cdr!    t    ) sp
  elim t (absurd₍-₎       ∷ sp) = elim (absurd! t    ) sp
  elim t (case₍-, u , v ₎ ∷ sp) = elim (case!   t u v) sp

nf : ∀ {Γ 𝔸} → Tm Γ 𝔸 → Nf Γ 𝔸
nf (var    x    ) = var! x
nf (sole        ) = sole
nf (cons   t u  ) = cons    (nf t) (nf u)
nf (car    t    ) = car!    (nf t)
nf (cdr    t    ) = cdr!    (nf t)
nf (lam    t    ) = lam     (nf t)
nf (app    t u  ) = app!    (nf t) (nf u)
nf (absurd t    ) = absurd! (nf t)
nf (left   t    ) = left    (nf t)
nf (right  t    ) = right   (nf t)
nf (case   t u v) = case!   (nf t) (nf u) (nf v)
