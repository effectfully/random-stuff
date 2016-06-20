{-# OPTIONS --type-in-type #-}

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Unit.Base
open import Data.Product

_∸>_ : ∀ {I} -> (I -> Set) -> (I -> Set) -> Set
A ∸> B = ∀ {i} -> A i -> B i

data Desc I (R : I -> Set) : Set

Arg : Set -> Set
Arg I = Desc I (const ⊤)

⟦_⟧ : ∀ {I} -> Arg I -> (I -> Set) -> Set

data Desc I R where
  ret : ∀ i -> R i -> Desc I R
  π   : ∀ A -> (A -> Desc I R) -> Desc I R
  σ   : ∀ D -> (⟦ D ⟧ R -> Desc I R) -> Desc I R

pattern ind i = ret i tt

⟦ ind i ⟧ B = B i
⟦ π A D ⟧ B = ∀   x -> ⟦ D x ⟧ B
⟦ σ D E ⟧ B = ∃ λ x -> ⟦ E x ⟧ B

imap : ∀ {I B C} -> (B ∸> C) -> (D : Arg I) -> ⟦ D ⟧ B -> ⟦ D ⟧ C
imap g (ret i r)  y      = g y
imap g (π A D)    f      = λ x -> imap g (D x) (f x)
imap g (σ D E)   (r , y) = r , imap g (E r) y

Extend : ∀ {I R} -> Desc I R -> (B : I -> Set) -> (B ∸> R) -> I -> Set
Extend (ret i r) B g j = i ≡ j
Extend (π A D)   B g j = ∃ λ x -> Extend (D  x)           B g j
Extend (σ D E)   B g j = ∃ λ x -> Extend (E (imap g D x)) B g j

{-# TERMINATING #-}
mutual
  data μ {I R} (D : Desc I R) j : Set where
    node : Extend D (μ D) eval j -> μ D j

  eval : ∀ {I R} {D : Desc I R} -> μ D ∸> R
  eval {D = D} (node e) = evalExtend D e

  evalExtend : ∀ {I R} ({D} E : Desc I R) -> Extend E (μ D) eval ∸> R
  evalExtend (ret i r)  refl   = r
  evalExtend (π A D)   (x , e) = evalExtend (D  x)              e
  evalExtend (σ D E)   (r , e) = evalExtend (E (imap eval D r)) e



data Descᵗ : Set where
  retᵗ πᵗ ⊛ᵗ : Descᵗ

Desc′ : ∀ I -> (I -> Set) -> Set
Desc′ I = μ $ π Descᵗ λ
  { retᵗ -> π (I -> Set) λ R ->
              π I λ i ->
                π (R i) λ _ ->
                  ret R (_$ i)
  ; πᵗ   -> π (I -> Set) λ R ->
              π Set λ A ->
                σ (π A λ _ -> ind R) λ D ->
                  ret R (λ B -> ∀ x -> D x B)
  ; ⊛ᵗ   -> π (I -> Set) λ R ->
              σ (ind (const ⊤)) λ D ->
                σ (π (D R) λ _ -> ind R) λ E ->
                  ret R (λ B -> Σ (D R) (λ r -> E r B))
  }

mutual
  toDesc′ : ∀ {I R} -> Desc I R -> Desc′ I R
  toDesc′ (ret i r) = node (retᵗ , _ , i , r , refl)
  toDesc′ (π A D)   = node (πᵗ , _ , A , (λ x -> toDesc′ (D x)) , refl)
  toDesc′ (σ D E)   = node (⊛ᵗ , _ , toDesc′ D , (λ r -> toDesc′ (E (coe D r))) , refl)

  coe : ∀ {I R} -> (D : Arg I) -> eval (toDesc′ D) R -> ⟦ D ⟧ R 
  coe (ret i _)  r      = r
  coe (π A D)    f      = λ x -> coe (D x) (f x)
  coe (σ D E)   (t , r) = coe D t , coe (E (coe D t)) r
