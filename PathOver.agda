infix 3 [_]_≅_

data [_]_≅_ {ι α} {I : Set ι} {i} (A : I -> Set α) (x : A i) : ∀ {j} -> A j -> Set where
  refl : [ A ] x ≅ x

cong : ∀ {ι α β} {I : Set ι} {A : I -> Set α} {B : I -> Set β} {i j} {x : A i} {y : A j}
     -> (f : ∀ {i} -> A i -> B i) -> [ A ] x ≅ y -> [ B ] f x ≅ f y
cong f refl = refl

congᵏ : ∀ {ι α β} {I : Set ι} {A : I -> Set α} {B : I -> Set β}
          {k : I -> I} {i j} {x : A i} {y : A j}
      -> (f : ∀ {i} -> A i -> B (k i)) -> [ A ] x ≅ y -> [ B ] f x ≅ f y
congᵏ f refl = refl

subst : ∀ {ι α β} {I : Set ι} {A : I -> Set α} {i j} {x : A i} {y : A j}
      -> (B : ∀ {i} -> A i -> Set β) -> [ A ] x ≅ y -> B x -> B y
subst B refl z = z

open import Data.Nat.Base
open import Data.Vec

assoc : ∀ {α n m p} {A : Set α} {zs : Vec A p}
      -> (xs : Vec A n) -> (ys : Vec A m) -> [ Vec A ] (xs ++ ys) ++ zs ≅ xs ++ ys ++ zs
assoc  []      ys = refl
assoc (x ∷ xs) ys = congᵏ (x ∷_) (assoc xs ys)

example : ∀ {n}
        -> (C : ∀ {n} -> Vec ℕ n -> Set)
        -> (xs ys {zs} : Vec ℕ n)
        -> C ((xs ++ ys) ++ zs)
        -> C (xs ++ ys ++ zs)
example C xs ys = subst C (assoc xs ys)
