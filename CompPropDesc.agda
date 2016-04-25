open import Level renaming (zero to lzero; suc to lsuc)
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product

data Desc {ι} (I : Set ι) : Set (lsuc lzero ⊔ ι) where
  var : I -> Desc I
  σ π : (A : Set) -> (A -> Desc I) -> Desc I
  _&_ : Desc I -> Desc I -> Desc I

⟦_⟧ : ∀ {ι} {I : Set ι} -> Desc I -> (I -> Set ι) -> Set ι
⟦ var i ⟧ F = F i
⟦ σ A B ⟧ F = ∃ λ x -> ⟦ B x ⟧ F
⟦ π A B ⟧ F = ∀   x -> ⟦ B x ⟧ F
⟦ D & E ⟧ F = ⟦ D ⟧ F × ⟦ E ⟧ F

Extend : ∀ {ι} {I : Set ι} -> Desc I -> (I -> Set ι) -> I -> Set ι
Extend (var j) F i = j ≡ i
Extend (σ A B) F i = ∃ λ x -> Extend (B x) F i
Extend (π A B) F i = ∀   x -> ⟦ B x ⟧ F
Extend (D & E) F i = ⟦ D ⟧ F × Extend E F i

record μ {I} (D : Desc I) i : Set where
  inductive
  constructor node
  field knot : Extend D (μ D) i



open import Data.Unit.Base
open import Data.Bool.Base
open import Data.Nat.Base

Vec : Set -> ℕ -> Set
Vec A = μ $ σ Bool λ b -> if b then var 0 else σ ℕ λ n -> σ A λ _ -> var n & var (suc n)

pattern []ᵥ           = node (true , refl)
pattern _∷ᵥ_ {n} x xs = node (false , n , x , xs , refl)

elimVec : ∀ {n π} {A}
        -> (P : ∀ {n} -> Vec A n -> Set π)
        -> (∀ {n} {xs : Vec A n} x -> P xs -> P (x ∷ᵥ xs))
        -> P []ᵥ
        -> (xs : Vec A n)
        -> P xs
elimVec P f z  []ᵥ      = z
elimVec P f z (x ∷ᵥ xs) = f x (elimVec P f z xs)



W : (A : Set) -> (A -> Set) -> Set
W A B = μ (σ A λ x -> π (B x) λ _ -> var tt) tt

pattern sup x g = node (x , g)

{-# TERMINATING #-} -- Why?
elimW : ∀ {π A B}
      -> (P : W A B -> Set π)
      -> (∀ {x} {g : B x -> W A B} -> (∀ y -> P (g y)) -> P (sup x g))
      -> ∀ w
      -> P w
elimW P h (sup x g) = h (λ y -> elimW P h (g y))
