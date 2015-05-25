-- Write some tests.

{-# OPTIONS --no-positivity-check #-}

open import Function
open import Data.Nat
open import Data.List

lookup : ∀ {α} {A : Set α} -> ℕ -> List A -> A
lookup  0      (x ∷ xs) = x
lookup (suc n) (x ∷ xs) = lookup n xs
lookup  _       _       = undefined where postulate undefined : _

data Type : Set where
  ⋆ : Type
  _⇒_ : Type -> Type -> Type

data Term : Set where
  var : ℕ -> Term
  ƛ   : Term -> Term
  _·_ : Term -> Term -> Term

data Neᴾ A : Set where
  varⁿ : ℕ -> Neᴾ A
  _·ⁿ_ : Neᴾ A -> A -> Neᴾ A

mutual
  data Nf : Set where
    ne : Ne -> Nf
    ƛⁿ : Nf -> Nf

  Ne = Neᴾ Nf

mutual
  embⁿᵉ : Ne -> Term
  embⁿᵉ (varⁿ i) = var i
  embⁿᵉ (f ·ⁿ x) = embⁿᵉ f · embⁿᶠ x

  embⁿᶠ : Nf -> Term
  embⁿᶠ (ne x) = embⁿᵉ x
  embⁿᶠ (ƛⁿ b) = ƛ (embⁿᶠ b)

data Valᴾ A : Set where
  v  : A -> Valᴾ A
  ƛᵛ : (Valᴾ A -> Valᴾ A) -> Valᴾ A

Con : Set -> Set
Con A = List (Valᴾ A)

_$ᵛ_ : ∀ {A} -> Valᴾ A -> Valᴾ A -> Valᴾ A
ƛᵛ f $ᵛ x = f x
v  x $ᵛ y = undefined where postulate undefined : _

⟦_⟧ : ∀ {A} -> Term -> Con A -> Valᴾ A
⟦ var i ⟧ ρ = lookup i ρ
⟦ ƛ b   ⟧ ρ = ƛᵛ λ x -> ⟦ b ⟧ (x ∷ ρ)
⟦ f · x ⟧ ρ = ⟦ f ⟧ ρ $ᵛ ⟦ x ⟧ ρ

normᴾ : ∀ {A} -> (Valᴾ A -> Nf) -> Term -> Term
normᴾ h x = embⁿᶠ (h (⟦ x ⟧ []))

module NbE where
  Ñf : Set
  Ñf = ℕ -> Nf

  Ñe : Set
  Ñe = ℕ -> Ne

  Val : Set
  Val = Valᴾ Ñf

  mutual
    reify : Type -> Val -> Ñf
    reify  ⋆      (v x)  = x
    reify (σ ⇒ τ) (ƛᵛ f) = λ i -> ƛⁿ (reify τ (f (reflect σ (λ j -> varⁿ (j ∸ i ∸ 1)))) (suc i))
    reify  _       _     = undefined where postulate undefined : _
    
    reflect : Type -> Ñe -> Val
    reflect  ⋆      x = v (ne ∘ x)
    reflect (σ ⇒ τ) f = ƛᵛ λ x -> reflect τ (λ i -> f i ·ⁿ reify σ x i)

  norm : Type -> Term -> Term
  norm σ = normᴾ (λ v -> reify σ v 0)

module BSN where
  record Fix (A : Set -> Set) : Set where
    constructor F
    field x : A (Fix A)

  Val : Set
  Val = Fix (Valᴾ ∘ Neᴾ)

  Neᵛ : Set
  Neᵛ = Neᴾ Val

  mutual
    quoteᵛ : ℕ -> Val -> Nf
    quoteᵛ i (F (v  x)) = ne (quoteⁿ i x)
    quoteᵛ i (F (ƛᵛ f)) = ƛⁿ (quoteᵛ (suc i) (F (f (v (varⁿ i)))))

    quoteⁿ : ℕ -> Neᵛ -> Ne
    quoteⁿ i (varⁿ j) = varⁿ (j ∸ i ∸ 1)
    quoteⁿ i (f ·ⁿ x) = quoteⁿ i f ·ⁿ quoteᵛ i x

  norm : Term -> Term
  norm = normᴾ (quoteᵛ 0 ∘ F)
