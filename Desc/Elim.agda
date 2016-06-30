open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Product

infixr 5 _⊕_
infixr 6 _⊛_

data Desc (I : Set) : Set₁ where
  var     : I -> Desc I
  π       : (A : Set) -> (A -> Desc I) -> Desc I
  _⊕_ _⊛_ : Desc I -> Desc I -> Desc I

⟦_⟧ : ∀ {I} -> Desc I -> (I -> Set) -> Set
⟦ var i ⟧ B = B i
⟦ π A D ⟧ B = ∀ x -> ⟦ D x ⟧ B
⟦ D ⊕ E ⟧ B = ⟦ D ⟧ B ⊎ ⟦ E ⟧ B
⟦ D ⊛ E ⟧ B = ⟦ D ⟧ B × ⟦ E ⟧ B

Extend : ∀ {I} -> Desc I -> (I -> Set) -> I -> Set
Extend (var i) B j = i ≡ j
Extend (π A D) B j = ∃ λ x -> Extend (D x) B j
Extend (D ⊕ E) B j = Extend D B j ⊎ Extend E B j
Extend (D ⊛ E) B j = ⟦ D ⟧ B × Extend E B j

data μ {I} (D : Desc I) j : Set where
  node : Extend D (μ D) j -> μ D j

Hyp : ∀ {I B} -> (∀ {i} -> B i -> Set) -> (D : Desc I) -> ⟦ D ⟧ B -> Set
Hyp C (var i)  y      = C y
Hyp C (π A D)  f      = ∀ x -> Hyp C (D x) (f x)
Hyp C (D ⊕ E)  s      = [ Hyp C D , Hyp C E ]′ s
Hyp C (D ⊛ E) (x , y) = Hyp C D x × Hyp C E y

Elim : ∀ {I B} -> (∀ {i} -> B i -> Set) -> (D : Desc I) -> (∀ {j} -> Extend D B j -> B j) -> Set
Elim C (var i) k = C (k refl)
Elim C (π A D) k = ∀ x -> Elim C (D x) (k ∘ _,_ x)
Elim C (D ⊕ E) k = Elim C D (k ∘ inj₁) × Elim C E (k ∘ inj₂)
Elim C (D ⊛ E) k = ∀ {x} -> Hyp C D x -> Elim C E (k ∘ _,_ x)

module _ {I} {D₀ : Desc I} (P : ∀ {j} -> μ D₀ j -> Set) (f₀ : Elim P D₀ node) where
  mutual
    elimExtend : ∀ {j}
               -> (D : Desc I) {k : ∀ {j} -> Extend D (μ D₀) j -> μ D₀ j}
               -> Elim P D k
               -> (e : Extend D (μ D₀) j)
               -> P (k e)
    elimExtend (var i)  z       refl    = z
    elimExtend (π A D)  f      (x , e)  = elimExtend (D x) (f  x) e
    elimExtend (D ⊕ E) (f , g) (inj₁ x) = elimExtend D f x
    elimExtend (D ⊕ E) (f , g) (inj₂ y) = elimExtend E g y
    elimExtend (D ⊛ E)  f      (d , e)  = elimExtend E (f (hyp D d)) e

    hyp : ∀ D -> (d : ⟦ D ⟧ (μ D₀)) -> Hyp P D d
    hyp (var i)  d       = elim d
    hyp (π A D)  f       = λ x -> hyp (D x) (f x)
    hyp (D ⊕ E) (inj₁ x) = hyp D x
    hyp (D ⊕ E) (inj₂ y) = hyp E y  
    hyp (D ⊛ E) (x , y)  = hyp D x , hyp E y

    elim : ∀ {j} -> (d : μ D₀ j) -> P d
    elim (node e) = elimExtend D₀ f₀ e



open import Data.Unit.Base
open import Data.Nat.Base



vec : Set -> Desc ℕ
vec A = var 0
      ⊕ π ℕ λ n -> π A λ _ -> var n ⊛ var (suc n)

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



W : (A : Set) -> (A -> Set) -> Set
W A B = μ (π A λ x -> (π (B x) λ _ -> var tt) ⊛ var tt) tt

pattern sup x g = node (x , g , refl)

elimW : ∀ {A B}
      -> (P : W A B -> Set)
      -> (∀ {x} {g : B x -> W A B} -> (∀ y -> P (g y)) -> P (sup x g))
      -> ∀ w
      -> P w
elimW P h = elim P (λ _ -> h)
