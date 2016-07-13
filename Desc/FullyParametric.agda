module _ where

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Unit.Base
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Sum
open import Data.Product

module ParamDesc (P : Set) where
  infixr 5 _⊕_
  infixr 6 _⊛_

  data Desc (I : Set) : Set₁ where
    var     : (P -> I) -> Desc I
    π       : (A : P -> Set) -> ((∀ p -> A p) -> Desc I) -> Desc I
    _⊕_ _⊛_ : Desc I -> Desc I -> Desc I

module _ {P : Set} where
  open ParamDesc P

  ⟦_⟧ : ∀ {I} -> Desc I -> (P -> I -> Set) -> P -> Set
  ⟦ var i ⟧ B p = B p (i p)
  ⟦ π A D ⟧ B p = ∀ x -> ⟦ D x ⟧ B p
  ⟦ D ⊕ E ⟧ B p = ⟦ D ⟧ B p ⊎ ⟦ E ⟧ B p
  ⟦ D ⊛ E ⟧ B p = ⟦ D ⟧ B p × ⟦ E ⟧ B p

  Extend : ∀ {I} -> Desc I -> (P -> I -> Set) -> P -> I -> Set
  Extend (var i) B p j = i p ≡ j
  Extend (π A D) B p j = ∃ λ x -> Extend (D x) B p j
  Extend (D ⊕ E) B p j = Extend D B p j ⊎ Extend E B p j
  Extend (D ⊛ E) B p j = ⟦ D ⟧ B p × Extend E B p j

  data μ {I} (D : Desc I) p j : Set where
    node : Extend D (μ D) p j -> μ D p j



  vec : Set -> Desc ℕ
  vec A = var (const 0)
        ⊕ π (const ℕ) λ n -> π (const A) λ _ -> var n ⊛ var (suc ∘ n)

Vec : Set -> ℕ -> Set
Vec A = μ (vec A) tt

pattern []           = node (inj₁ refl)
pattern _∷_ {n} x xs = node (inj₂ (n , x , xs , refl))

elimVec : ∀ {n A}
        -> (P : ∀ {n} -> Vec A n -> Set)
        -> (∀ {n} x {xs : Vec A n} -> P xs -> P (x ∷ xs))
        -> P []
        -> (xs : Vec A n)
        -> P xs
elimVec P f z  []      = z
elimVec P f z (x ∷ xs) = f x (elimVec P f z xs)
