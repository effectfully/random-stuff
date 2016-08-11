{-# OPTIONS --type-in-type --rewriting #-}

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (map)

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

  open import Relation.Binary.PropositionalEquality.TrustMe

  coh = pointwise (init p (λ xs -> proj₁ (proj₁ (xs cons nil))) (λ _ _ -> refl) refl) trustMe
  
map : ∀ {A B} -> (A -> B) -> List A -> List B
map f = elimList _ (_∷_ ∘ f) []

subst-compute : ∀ {I A} {i j : I} {x : A} -> (p : i ≡ j) -> subst (const A) p x ≡ x
subst-compute refl = refl

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE subst-compute #-}

map-map : ∀ {A B C} {f : A -> B} {g : B -> C} -> map g ∘ map f ≗ map (g ∘ f)
map-map {f = f} {g} = elimList (λ xs -> map g (map f xs) ≡ map (g ∘ f) xs)
                               (λ x -> cong (g (f x) ∷_))
                                refl

open import Data.Nat.Base
open import Data.Vec renaming ([] to []ᵥ; _∷_ to _∷ᵥ_) hiding (toList)

length : ∀ {A} -> List A -> ℕ
length = elimList _ (const suc) 0

toVec : ∀ {A} -> (xs : List A) -> Vec A (length xs)
toVec = elimList (Vec _ ∘ length) _∷ᵥ_ []ᵥ

toList : ∀ {A n} -> Vec A n -> List A
toList = foldr _ _∷_ []

-- We need a more complicated computational rule for `subst` to prove this lemma.
toList-toVec : ∀ {A} -> toList ∘ toVec {A} ≗ id
toList-toVec = elimList (λ xs -> toList (toVec xs) ≡ xs) (λ x r -> {!!}) refl

-- Is this enough for all cases? I doubt.
subst-compute₂ : ∀ {I B} {i j : I}
               -> (A : I -> Set)
               -> (p : i ≡ j)
               -> (x : A i)
               -> (f : ∀ {k} -> A k -> B)
               -> f (subst A p x) ≡ f x
subst-compute₂ A refl x f = refl
