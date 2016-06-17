-- The final version.

{-# OPTIONS --type-in-type #-}

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product

data Desc I : Set where
  var : I -> Desc I
  π   : ∀ A -> (A -> Desc I) -> Desc I
  _⊛_ : Desc I -> Desc I -> Desc I

⟦_⟧ : ∀ {I} -> Desc I -> (I -> Set) -> Set
⟦ var i ⟧ B = B i
⟦ π A D ⟧ B = ∀ x -> ⟦ D x ⟧ B
⟦ D ⊛ E ⟧ B = ⟦ D ⟧ B × ⟦ E ⟧ B

Extend : ∀ {I} -> Desc I -> (I -> Set) -> I -> Set
Extend (var i) B j = i ≡ j
Extend (π A D) B i = ∃ λ x -> Extend (D x) B i
Extend (D ⊛ E) B i = ⟦ D ⟧ B × Extend E B i

data μ {I} (D : Desc I) j : Set where
  node : Extend D (μ D) j -> μ D j

Hyp : ∀ {I B} -> (∀ {i} -> B i -> Set) -> (D : Desc I) -> ⟦ D ⟧ B -> Set
Hyp C (var i)  y      = C y
Hyp C (π A D)  f      = ∀ x -> Hyp C (D x) (f x) 
Hyp C (D ⊛ E) (x , y) = Hyp C D x × Hyp C E y

Elim : ∀ {I B} -> (∀ {i} -> B i -> Set) -> (D : Desc I) -> (∀ {j} -> Extend D B j -> B j) -> Set
Elim C (var i) k = C (k refl)
Elim C (π A D) k = ∀ x -> Elim C (D x) (k ∘ _,_ x)
Elim C (D ⊛ E) k = ∀ {x} -> Hyp C D x -> Elim C E (k ∘ _,_ x)

module _ {I} {D₀ : Desc I} (P : ∀ {j} -> μ D₀ j -> Set) (h : Elim P D₀ node) where
  mutual
    elimExtend : ∀ {j}
               -> (D : Desc I) {k : ∀ {j} -> Extend D (μ D₀) j -> μ D₀ j}
               -> Elim P D k
               -> (e : Extend D (μ D₀) j)
               -> P (k e)
    elimExtend (var i) z  refl   = z
    elimExtend (π A D) h (x , e) = elimExtend (D x) (h  x)        e
    elimExtend (D ⊛ E) h (d , e) = elimExtend  E    (h (hyp D d)) e

    hyp : ∀ D -> (d : ⟦ D ⟧ (μ D₀)) -> Hyp P D d
    hyp (var i)  d      = elim d
    hyp (π A D)  f      = λ x -> hyp (D x) (f x)
    hyp (D ⊛ E) (x , y) = hyp D x , hyp E y

    elim : ∀ {j} -> (d : μ D₀ j) -> P d
    elim (node e) = elimExtend D₀ h e
