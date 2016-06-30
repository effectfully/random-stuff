open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Product

infixr 5 _⊕_

data Desc (I : Set) : Set₁ where
  ret : I -> Desc I
  π   : (A : Set) -> (A -> Desc I) -> Desc I
  _⊕_ : Desc I -> Desc I -> Desc I
  ind : I -> Desc I -> Desc I

⟦_⟧ : ∀ {I} -> Desc I -> (I -> Set) -> I -> Set
⟦ ret i   ⟧ B j = i ≡ j
⟦ π A D   ⟧ B j = ∃ λ x -> ⟦ D x ⟧ B j
⟦ D ⊕ E   ⟧ B j = ⟦ D ⟧ B j ⊎ ⟦ E ⟧ B j
⟦ ind i D ⟧ B j = B i × ⟦ D ⟧ B j

data μ {I} (D : Desc I) j : Set where
  node : ⟦ D ⟧ (μ D) j -> μ D j

Elim : ∀ {I B} -> (∀ {i} -> B i -> Set) -> (D : Desc I) -> (∀ {j} -> ⟦ D ⟧ B j -> B j) -> Set
Elim C (ret i)   k = C (k refl)
Elim C (π A D)   k = ∀ x -> Elim C (D x) (k ∘ _,_ x)
Elim C (D ⊕ E)   k = Elim C D (k ∘ inj₁) × Elim C E (k ∘ inj₂)
Elim C (ind i D) k = ∀ {y} -> C y -> Elim C D (k ∘ _,_ y)

module _ {I} {D₀ : Desc I} (P : ∀ {j} -> μ D₀ j -> Set) (f₀ : Elim P D₀ node) where
  mutual
    elimSem : ∀ {j}
            -> (D : Desc I) {k : ∀ {j} -> ⟦ D ⟧ (μ D₀) j -> μ D₀ j}
            -> Elim P D k
            -> (e : ⟦ D ⟧ (μ D₀) j)
            -> P (k e)
    elimSem (ret i)    z       refl    = z
    elimSem (π A D)    f      (x , e)  = elimSem (D x) (f  x) e
    elimSem (D ⊕ E)   (f , g) (inj₁ x) = elimSem D f x
    elimSem (D ⊕ E)   (f , g) (inj₂ y) = elimSem E g y
    elimSem (ind i D)  f      (d , e)  = elimSem D (f (elim d)) e

    elim : ∀ {j} -> (d : μ D₀ j) -> P d
    elim (node e) = elimSem D₀ f₀ e



open import Data.Unit.Base
open import Data.Nat.Base

vec : Set -> Desc ℕ
vec A = ret 0
      ⊕ π ℕ λ n -> π A λ _ -> ind n $ ret (suc n)

Vec : Set -> ℕ -> Set
Vec A = μ (vec A)

pattern []           = node (inj₁ refl)
pattern _∷_ {n} x xs = node (inj₂ (n , x , xs , refl))

elimVec : ∀ {n A}
        -> (P : ∀ {n} -> Vec A n -> Set)
        -> (∀ {n} x {xs : Vec A n} -> P xs -> P (x ∷ xs))
        -> P []
        -> (xs : Vec A n)
        -> P xs
elimVec P f z = elim P (z , λ _ -> f)
