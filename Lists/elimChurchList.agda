{-# OPTIONS --type-in-type #-}

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product

infixr 5 _∷′_ _∷_

List′ : Set -> Set
List′ A = ∀ {B} -> (A -> B -> B) -> B -> B

[]′ : ∀ {A} -> List′ A
[]′ = λ f z -> z

_∷′_ : ∀ {A} -> A -> List′ A -> List′ A
x ∷′ xs = λ f z -> f x (xs f z)

Univ : ∀ {A} -> List′ A -> Set
Univ {A} xs = ∀ {B}
            -> (h′ : List′ A -> B)
            -> (f : A -> B -> B)
            -> (z : B)
            -> (∀ x (xs : List′ A) -> h′ (x ∷′ xs) ≡ f x (h′ xs))
            -> h′ []′ ≡ z
            -> h′ xs ≡ xs f z

List : Set -> Set
List A = Σ (List′ A) Univ

init : ∀ {A}
     -> (p : List A)
     -> (h′ : List′ A -> List′ A)
     -> (∀ x (xs : List′ A) -> (λ {B} -> h′ (x ∷′ xs) {B}) ≡ x ∷′ h′ xs)
     -> (λ {B} -> h′ []′ {B}) ≡ []′
     -> (λ {B} -> h′ (proj₁ p) {B}) ≡ proj₁ p
init (xs , u) h′ q r = trans (u h′ _∷′_ []′ q r) (sym (u id _∷′_ []′ (λ _ _ -> refl) refl))

[] : ∀ {A} -> List A
[] = []′ , λ h′ f z q r -> r

_∷_ : ∀ {A} -> A -> List A -> List A
x ∷ (xs , u) = x ∷′ xs , λ h′ f z q r -> trans (q x xs) (cong (f x) (u h′ f z q r))

elimList′ : ∀ {A}
          -> (P : List′ A -> Set)
          -> (∀ {xs : List′ A} x -> P xs -> P (x ∷′ xs))
          -> P []′
          -> (xs : List A)
          -> P (proj₁ xs)
elimList′ {A} P f z p@(xs , u) = subst P coh (proj₂ (xs cons nil)) where
  cons : A -> ∃ P -> ∃ P
  cons x (xs , r) = x ∷′ xs , f x r

  nil : ∃ P
  nil = []′ , z

  coh = init p (λ xs -> proj₁ (xs cons nil)) (λ _ _ -> refl) refl

pointwise : {A : Set} {B : A -> Set} {p₁ p₂ : Σ A B}
          -> (q : proj₁ p₁ ≡ proj₁ p₂)
          -> subst B q (proj₂ p₁) ≡ proj₂ p₂
          -> p₁ ≡ p₂
pointwise refl refl = refl

postulate contr : {A : Set} -> A

elimList : ∀ {A}
         -> (P : List A -> Set)
         -> (∀ {xs : List A} x -> P xs -> P (x ∷ xs))
         -> P []
         -> (xs : List A)
         -> P xs
elimList {A} P f z p@(xs , u) = subst P coh (proj₂ (xs cons nil)) where
  cons : A -> ∃ P -> ∃ P
  cons x (xs , r) = x ∷ xs , f x r

  nil : ∃ P
  nil = [] , z

  coh = pointwise (init p (λ xs -> proj₁ (proj₁ (xs cons nil))) (λ _ _ -> refl) refl) contr
