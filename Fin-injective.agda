-- This is inspired by https://github.com/luqui/experiments/blob/master/Fin-inj.agda

open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using (refl ; _≅_ ; _≇_ )
open import Data.Empty
open import Data.Nat
open import Data.Fin as F hiding (_+_)
open import Data.Nat.Properties.Simple

unsubst : ∀ {α γ} {A : Set α} {C : A -> Set γ} {i j : A} (p : i ≡ j) {x : C i} {y : C j}
        -> subst C p x ≡ y -> x ≅ y
unsubst refl refl = refl

suc-inv : ∀ {n m} {i : Fin n} {j : Fin m} -> F.suc i ≅ F.suc j -> i ≅ j
suc-inv refl = refl

fromℕ-+-neq : ∀ {n} m (i : Fin n) -> fromℕ (n + m) ≇ i 
fromℕ-+-neq {0}     m  ()     q
fromℕ-+-neq {suc n} m  zero   ()
fromℕ-+-neq {suc n} m (suc i) q = fromℕ-+-neq m i (suc-inv q)

Fin-suc-+-neq : ∀ n m -> Fin (suc n + m) ≢ Fin n
Fin-suc-+-neq n m q with subst id q (fromℕ (n + m)) | inspect (subst id q) (fromℕ (n + m))
... | i | [ r ] = fromℕ-+-neq m i (unsubst q r)

decrease-Fin : ∀ {n m} p -> Fin (suc p + n) ≡ Fin (suc p + m) -> Fin (p + n) ≡ Fin (p + m)
decrease-Fin {0}     {0}     p q = refl
decrease-Fin {suc n} {0}     p q rewrite +-right-identity p | +-suc p n =
  ⊥-elim (Fin-suc-+-neq (suc p) n q)
decrease-Fin {0}     {suc m} p q rewrite +-right-identity p | +-suc p m =
  ⊥-elim (Fin-suc-+-neq (suc p) m (sym q))
decrease-Fin {suc n} {suc m} p q rewrite  +-suc p n | +-suc p m = decrease-Fin (suc p) q

Fin-neq : ∀ {n m} -> n ≢ m -> Fin n ≢ Fin m
Fin-neq {0}     {0}     ¬q = λ _ -> ¬q refl
Fin-neq {suc n} {0}     ¬q = Fin-suc-+-neq 0 n
Fin-neq {0}     {suc m} ¬q = Fin-suc-+-neq 0 m ∘ sym
Fin-neq {suc n} {suc m} ¬q = Fin-neq (¬q ∘ cong suc) ∘ decrease-Fin 0

Fin-injective : ∀ {n m} -> Fin n ≡ Fin m -> n ≡ m
Fin-injective {n} {m} q with n ≟ m
... | yes r = r
... | no  r = ⊥-elim (Fin-neq r q)
