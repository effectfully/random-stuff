open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality
open import Data.Bool.Base
open import Data.Nat.Base using (ℕ)
open import Data.Product

_∸>_ : ∀ {ι α β} {I : Set ι} -> (I -> Set α) -> (I -> Set β) -> Set (ι ⊔ α ⊔ β)
A ∸> B = ∀ {i} -> A i -> B i

mutual
  data Univ : Set where
    bool nat : Univ
    π : ∀ A -> (⟦ A ⟧ -> Univ) -> Univ

  ⟦_⟧ : Univ -> Set
  ⟦ bool  ⟧ = Bool
  ⟦ nat   ⟧ = ℕ
  ⟦ π A B ⟧ = ∀ x -> ⟦ B x ⟧

data Tel : Set where
  end : Tel
  sig : (A : Univ) -> (⟦ A ⟧ -> Tel) -> Tel

_->ₜ_ : ∀ {β} -> Tel -> Set β -> Set β
end     ->ₜ B = B
sig A K ->ₜ B = ∀ x -> K x ->ₜ B

Πₜ : ∀ {β γ} {B : Set β} T -> (B -> Set γ) -> (T ->ₜ B) -> Set γ
Πₜ  end      C y = C y
Πₜ (sig A K) C f = ∀ x -> Πₜ (K x) C (f x)

fmapΠₜ : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : A -> Set γ}
       -> ∀ T {k : T ->ₜ A} -> (B ∸> C) -> Πₜ T B k -> Πₜ T C k
fmapΠₜ  end      g y = g y
fmapΠₜ (sig A K) g f = λ x -> fmapΠₜ (K x) g (f x)

data Desc (I : Set) (R : I -> Set) : Set where
  ret : ∀ j -> R j -> Desc I R
  pi  : ∀ A -> (⟦ A ⟧ -> Desc I R) -> Desc I R
  rpi : ∀ T -> (k : T ->ₜ I) -> (Πₜ T R k -> Desc I R) -> Desc I R

Extend : ∀ {I R} -> Desc I R -> (P : I -> Set) -> (P ∸> R) -> I -> Set
Extend (ret i r)   P g j = i ≡ j
Extend (pi  A B)   P g j = ∃ λ x -> Extend (B x) P g j
Extend (rpi T k B) P g j = ∃ λ (y : Πₜ T P k) -> Extend (B (fmapΠₜ T g y)) P g j

Coercible : {I : Set} -> (I -> Set) -> Set
Coercible R = ∀ {i j} -> i ≡ j -> R i -> R j

module CoeData {I R} (coe : Coercible R) where
  {-# TERMINATING #-} -- I refuse to manually inline `fmapΠₜ'.
  mutual
    record Data (D : Desc I R) i : Set where
      inductive
      constructor node
      field tree : Extend D (Data D) eval i

    eval : {D : Desc I R} -> Data D ∸> R
    eval {D} (node t) = evalExtend D t

    evalExtend : ({E} D : Desc I R) -> Extend D (Data E) eval ∸> R
    evalExtend (ret i r)    q      = coe q r
    evalExtend (pi  A B)   (x , t) = evalExtend (B x) t
    evalExtend (rpi T k B) (y , t) = evalExtend (B (fmapΠₜ T eval y)) t

  coerceExtend : ∀ {i j}
               -> ({E} D : Desc I R)
               -> i ≡ j
               -> Extend D (Data E) eval i
               -> Extend D (Data E) eval j
  coerceExtend (ret i r)   q₁  q₂     = trans q₂ q₁
  coerceExtend (pi  A B)   q₁ (x , t) = x , coerceExtend (B x) q₁ t
  coerceExtend (rpi T k B) q₁ (y , t) = y , coerceExtend (B (fmapΠₜ T eval y)) q₁ t

  coerce : ∀ {D : Desc I R} {i j} -> i ≡ j -> Data D i -> Data D j
  coerce {D} q (node t) = node (coerceExtend D q t)



open import Function
open import Data.Unit.Base

open CoeData {⊤} {λ _ -> Univ} (λ _ A -> A)

U : Set
U = Data (pi bool λ
  { true  -> ret tt nat
  ; false -> rpi end tt λ A -> rpi (sig A λ _ -> end) (λ _ -> tt) λ B -> ret tt (π A B)
  }) tt

pattern unat   = node (true , refl)
pattern uπ A B = node (false , A , B , refl)

{-# TERMINATING #-}
elimU : ∀ {π}
      -> (P : U -> Set π)
      -> (∀ {A B} -> P A -> (∀ x -> P (B x)) -> P (uπ A B))
      -> P unat
      -> ∀ A
      -> P A
elimU P h z  unat    = z
elimU P h z (uπ A B) = h (elimU P h z A) (elimU P h z ∘ B)
