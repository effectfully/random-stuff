-- The non-strictly-positive part is taken from
-- http://code.haskell.org/~dolio/agda-share/PHOASNorm.agda

-- This is for the non-strictly-positive part.
{-# OPTIONS --no-termination-check #-}

open import Function

infixr 6 _⇒_

data Type : Set where
  ⋆   : Type
  _⇒_ : Type -> Type -> Type

module _ (A : Type -> Set) where
  mutual
    data Term : Type -> Set where
      unit : Term ⋆
      lam  : ∀ {σ τ} -> (A σ -> Term τ) -> Term (σ ⇒ τ)
      app  : ∀ {σ} -> A σ -> Spine σ -> Term ⋆

    data Spine : Type -> Set where
      ø   : Spine ⋆
      _◁_ : ∀ {σ τ} -> Term σ -> Spine τ -> Spine (σ ⇒ τ)

mapSpine : ∀ {A B σ} -> (∀ {σ} -> Term A σ -> Term B σ) -> Spine A σ -> Spine B σ
mapSpine f  ø       = ø
mapSpine f (x ◁ xs) = f x ◁ mapSpine f xs

module NonStrictilyPositive where
  {-# NO_POSITIVITY_CHECK #-}
  data Knot (A : Type -> Set) σ : Set where
    var : A σ -> Knot A σ
    tie : Term (Knot A) σ -> Knot A σ

  apply : ∀ {A σ} -> Term (Knot A) σ -> Spine (Knot A) σ -> Term (Knot A) ⋆
  apply  x       ø       = x
  apply (lam k) (x ◁ xs) = apply (k (tie x)) xs

  norm : ∀ {A σ} -> Term (Knot A) σ -> Term (Knot A) σ
  norm  unit            = unit
  norm (lam k)          = lam λ x -> norm (k x)
  norm (app (var f) xs) = app (var f) (mapSpine norm xs)
  norm (app (tie f) xs) = apply (norm f) (mapSpine norm xs)

  flatten : ∀ {A σ} -> Term (Knot A) σ -> Term A σ
  flatten  unit            = unit
  flatten (lam k)          = lam λ x -> flatten (k (var x))
  flatten (app (var f) xs) = app f (mapSpine flatten xs)
  flatten (app (tie f) xs) = flatten (apply f xs)

  normalize : ∀ {A σ} -> Term (Knot A) σ -> Term A σ
  normalize = flatten ∘ norm

module StrictlyPositive where
  ⟦_/_⟧ : (Type -> Set) -> Type -> Set
  ⟦ A / ⋆     ⟧ = Term A ⋆
  ⟦ A / σ ⇒ τ ⟧ = ⟦ A / σ ⟧ -> ⟦ A / τ ⟧

  mutual
    eval : ∀ {A σ} -> Term ⟦ A /_⟧ σ -> ⟦ A / σ ⟧
    eval  unit      = unit
    eval (lam k)    = λ x -> eval (k x)
    eval (app f xs) = apply f xs

    apply : ∀ {A σ} -> ⟦ A / σ ⟧ -> Spine ⟦ A /_⟧ σ -> Term A ⋆
    apply k (x ◁ xs) = apply (k (eval x)) xs
    apply t  ø       = t

  mutual
    η* : ∀ {τ A} σ -> (Spine A σ -> Spine A τ) -> A τ -> ⟦ A / σ ⟧
    η*  ⋆      k v = app v (k ø)
    η* (σ ⇒ τ) k v = λ x -> η* τ (k ∘ (readback x ◁_)) v

    η : ∀ {A} σ -> A σ -> ⟦ A / σ ⟧
    η σ = η* σ id

    readback : ∀ {σ A} -> ⟦ A / σ ⟧ -> Term A σ
    readback {⋆}     t = t
    readback {σ ⇒ τ} k = lam (readback ∘ k ∘ η σ)

  join : ∀ {A σ} -> Term ⟦ A /_⟧ σ -> Term A σ
  join = readback ∘ eval

  Term⁺ : Type -> Set₁
  Term⁺ σ = ∀ {A} -> Term A σ 

  app⁺ : ∀ {A σ} -> Term⁺ σ -> Spine ⟦ A /_⟧ σ -> Term ⟦ A /_⟧ ⋆
  app⁺ f = app (eval f)

  A : ∀ {A} -> Term A ((⋆ ⇒ ⋆) ⇒ ⋆ ⇒ ⋆)
  A = lam λ f -> lam λ x -> app f (app x ø ◁ ø)

  I : ∀ {A} -> Term A (⋆ ⇒ ⋆)
  I = lam λ x -> app x ø

  open import Relation.Binary.PropositionalEquality

  I-unit : ∀ {A} -> Term ⟦ Term A /_⟧ ⋆
  I-unit = app⁺ I (unit ◁ ø)

  test : ∀ {A} -> join (I-unit {A}) ≡ unit
  test = refl
