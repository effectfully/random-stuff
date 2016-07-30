module _ where

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Unit.Base
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Sum
open import Data.Product

module Param (P : Set) where
  infixr 5 _⊕_
  infixr 6 _⊛_

  data Desc (I : Set) : Set₁ where
    var     : (P -> I) -> Desc I
    π       : (A : P -> Set) -> ((∀ p -> A p) -> Desc I) -> Desc I
    _⊕_ _⊛_ : Desc I -> Desc I -> Desc I

module _ where
  open Param ⊤

  ⟦_⟧ : ∀ {I} -> Desc I -> (I -> Set) -> Set
  ⟦ var i ⟧ B = B (i tt)
  ⟦ π A D ⟧ B = ∀ x -> ⟦ D x ⟧ B
  ⟦ D ⊕ E ⟧ B = ⟦ D ⟧ B ⊎ ⟦ E ⟧ B
  ⟦ D ⊛ E ⟧ B = ⟦ D ⟧ B × ⟦ E ⟧ B

  Extend : ∀ {I} -> Desc I -> (I -> Set) -> I -> Set
  Extend (var i) B j = i tt ≡ j
  Extend (π A D) B j = ∃ λ x -> Extend (D x) B j
  Extend (D ⊕ E) B j = Extend D B j ⊎ Extend E B j
  Extend (D ⊛ E) B j = ⟦ D ⟧ B × Extend E B j

  data μ {I} (D : Desc I) j : Set where
    node : Extend D (μ D) j -> μ D j

Desc : Set -> Set₁
Desc I = ∀ {P} -> Param.Desc P I

open Param hiding (Desc) public



vec : Set -> Desc ℕ
vec A = var (const 0)
      ⊕ π (const ℕ) λ n -> π (const A) λ _ -> var n ⊛ var (suc ∘ n)

Vec : Set -> ℕ -> Set
Vec A = μ (vec A)

pattern []           = node (inj₁  refl)
pattern _∷_ {n} x xs = node (inj₂ (n , x , xs , refl))

elimVec : ∀ {n A}
        -> (P : ∀ {n} -> Vec A n -> Set)
        -> (∀ {n} x {xs : Vec A n} -> P xs -> P (x ∷ xs))
        -> P []
        -> (xs : Vec A n)
        -> P xs
elimVec P f z  []      = z
elimVec P f z (x ∷ xs) = f x (elimVec P f z xs)
