{-# OPTIONS --rewriting #-}

open import Function
open import Relation.Binary.PropositionalEquality

{-# BUILTIN REWRITE _≡_ #-}

infixl 6 _·_
infixr 5 _⇒_

mutual
  data Type : Set₁ where
    emb : Set -> Type
    π   : ∀ A -> (⟦ A ⟧ᵗ -> Type) -> Type

  ⟦_⟧ᵗ : Type -> Set
  ⟦ emb A ⟧ᵗ = A
  ⟦ π A B ⟧ᵗ = ∀ x -> ⟦ B x ⟧ᵗ

mutual
  data Term : Type -> Set₁ where
    var : ∀ {A} -> ⟦ A ⟧ᵗ -> Term A
    _·_ : ∀ {A B} -> Term (π A B) -> (e : Term A) -> Term (B ⟦ e ⟧)
    lam : ∀ {A B} -> (∀ x -> Term (B x)) -> Term (π A B)

  ⟦_⟧ : ∀ {A} -> Term A -> ⟦ A ⟧ᵗ
  ⟦ var v ⟧ = v
  ⟦ f · x ⟧ = ⟦ f ⟧ ⟦ x ⟧
  ⟦ lam k ⟧ = λ x -> ⟦ k x ⟧

mutual
  data Ne : Type -> Set₁ where
    varⁿᵉ : ∀ {A} -> A -> Ne (emb A)
    _·ⁿᵉ_ : ∀ {A B} -> Ne (π A B) -> (e : NF A) -> Ne (B ⟦ e ⟧ⁿᶠ)

  data NF : Type -> Set₁ where
    neⁿᶠ  : ∀ {A} -> Ne A -> NF A
    lamⁿᶠ : ∀ {A B} -> (∀ x -> NF (B x)) -> NF (π A B)

  ⟦_⟧ⁿᵉ : ∀ {A} -> Ne A -> ⟦ A ⟧ᵗ
  ⟦_⟧ⁿᵉ = ⟦_⟧ ∘ embⁿᵉ

  ⟦_⟧ⁿᶠ : ∀ {A} -> NF A -> ⟦ A ⟧ᵗ
  ⟦_⟧ⁿᶠ = ⟦_⟧ ∘ embⁿᶠ

  embⁿᵉ : ∀ {A} -> Ne A -> Term A
  embⁿᵉ (varⁿᵉ v) = var v
  embⁿᵉ (f ·ⁿᵉ x) = embⁿᵉ f · embⁿᶠ x

  embⁿᶠ : ∀ {A} -> NF A -> Term A
  embⁿᶠ (neⁿᶠ n)  = embⁿᵉ n
  embⁿᶠ (lamⁿᶠ k) = lam λ x -> embⁿᶠ (k x)

module _ where
  ⟦_⟧ᵛ      : Type -> Set₁
  reify     : ∀ {A} -> ⟦ A ⟧ᵛ -> NF A
  unreflect : ∀ {A} -> ⟦ A ⟧ᵛ -> ⟦ A ⟧ᵗ
  reflect   : ∀ {A} -> ⟦ A ⟧ᵗ -> ⟦ A ⟧ᵛ

  unreflect = ⟦_⟧ⁿᶠ ∘ reify

  postulate
    unreflect-reflect : ∀ {A} (x : ⟦ A ⟧ᵗ) -> ⟦ embⁿᶠ (reify (reflect {A} x)) ⟧ ≡ x
  {-# REWRITE unreflect-reflect #-}

  ⟦ emb A ⟧ᵛ = Ne (emb A)
  ⟦ π A B ⟧ᵛ = ∀ x -> ⟦ B (unreflect {A} x) ⟧ᵛ

  reify {emb A} n = neⁿᶠ n
  reify {π A B} f = lamⁿᶠ λ x -> reify (f (reflect x))

  reflect {emb A} x = varⁿᵉ x
  reflect {π A B} f = λ x -> reflect (f (unreflect x))

read : ∀ {A} -> ⟦ A ⟧ᵗ -> Term A
read = embⁿᶠ ∘ reify ∘ reflect

norm : ∀ {A} -> Term A -> Term A
norm = read ∘ ⟦_⟧

_⇒_ : Type -> Type -> Type
A ⇒ B = π A λ _ -> B

I : ∀ {A} -> Term (A ⇒ A)
I = read id

K : ∀ {A B} -> Term (A ⇒ B ⇒ A)
K = read const

S : ∀ {A} {B : ⟦ A ⟧ᵗ -> Type} {C : ∀ {x} -> ⟦ B x ⟧ᵗ -> Type}
  -> Term ((π A λ x -> π (B x) λ y -> C y) ⇒ π (π A λ x -> B x) λ f -> π A λ x -> C (f x))
S = read _ˢ_

testS : ∀ {A B} {C : ∀ {x} -> ⟦ B x ⟧ᵗ -> Type} -> norm S ≡ S {A} {B} {C}
testS = refl

testSKI : ∀ {A} -> norm (S · K · I) ≡ I {A}
testSKI = refl
