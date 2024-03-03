module Prelude.Marker where
open import Prelude.Bool
open import Prelude.Equality
open import Prelude.Function
open import Prelude.Idiom
open import Prelude.List
open import Prelude.Maybe
open import Prelude.Nat
open import Prelude.Sigma
open import Prelude.Unit
open import Prelude.Reflection.Argument
open import Prelude.Reflection.Definition
open import Prelude.Reflection.Error
open import Prelude.Reflection.Monad
open import Prelude.Reflection.Term

private
  variable
    A : Set
    x y : A

⌜_⌝ : A → A
⌜ x ⌝ = x
{-# NOINLINE ⌜_⌝ #-}

abstract-marker : Term → Maybe Term
abstract-marker = go 0 where
  go  : Nat → Term → Maybe Term
  go* : Nat → List (Arg Term) → Maybe (List (Arg Term))

  go φ (var x ts) = if x < φ
                    then var      x  <$> go* φ ts
                    else var (suc x) <$> go* φ ts
  go φ (meta m ts) = meta m <$> go* φ ts
  go φ (con  c ts) = con  c <$> go* φ ts
  go φ (def d ts) with d
  ... | quote ⌜_⌝ = return $ var φ []
  ... | _         = def d <$> go* φ ts
  go φ (pi (arg i a) (abs x b)) = do
    a' ← go      φ  a
    b' ← go (suc φ) b
    return $ pi (arg i a') (abs x b')
  go φ (lam v (abs x t)) = lam v ∘ abs x <$> go (suc φ) t
  go φ (pat-lam cs ts) = nothing
  go φ (lit l) = return $ lit l
  go φ (sort s) with s
  ... | set t = sort ∘ set <$> go φ t
  ... | lit-set n = return $ sort (lit-set n)
  ... | inf-set n = return $ sort (inf-set n)
  ... | prop t = sort ∘ prop <$> go φ t
  ... | lit-prop n = return $ sort (lit-prop n)
  ... | unknown = return $ sort unknown
  go φ unknown = return $ unknown

  go* φ [] = return []
  go* φ (arg i t ∷ ts) = do
    t'  ← go  φ t
    ts' ← go* φ ts
    return $ arg i t' ∷ ts'

abstract-marker-error : Term → TC A
abstract-marker-error lhs = error $ str "Failed to abstract over marker in term: " ∷ term lhs ∷ []

pattern `cong f eq = def (quote cong) (f v∷ eq v∷ [])

macro
  cong! : x ≡ y → Term → TC ⊤
  cong! x≡y hole = do
    goal ← infer hole
    (lhs , rhs) ← get-boundary goal
    just t ← return $ abstract-marker lhs
      where nothing → abstract-marker-error lhs
    let f = vlam "-" t
    eq ← quote' x≡y
    unify hole $ `cong f eq

module _ {x y : A} {p : x ≡ y} {f : A → (A → A) → A} where
  private
    q : f x (λ y → x) ≡ f y (λ z → y)
    q =
      f ⌜ x ⌝ (λ _ → ⌜ x ⌝)  ≡⟨ cong! p ⟩
      f y (λ _ → y)          ∎

    r : f y (λ _ → y) ≡ f x (λ _ → x)
    r =
      f ⌜ y ⌝ (λ _ → ⌜ y ⌝)  ≡⟨ cong! (sym p) ⟩
      f x (λ _ → x)          ∎
