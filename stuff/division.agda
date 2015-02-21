-- related to http://stackoverflow.com/questions/28581814/how-to-define-division-operator-in-agda/

open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Product               hiding (map)
open import Data.List.Base
open import Induction.WellFounded
open import Induction.Nat
open import Data.Nat.Properties

calls : ∀ {a b ℓ} {A : Set a} {_<_ : Rel A ℓ} {guarded : A -> Set b}
      -> (f : A -> A)
      -> Well-founded _<_
      -> (∀ {x} -> guarded x -> f x < x)
      -> (∀ x -> Dec (guarded x))
      -> A
      -> List A
calls {A = A} {_<_} f wf smaller dec-guarded x = go (wf x) where
  go : ∀ {x} -> Acc _<_ x -> List A
  go {x} (acc r) with dec-guarded x
  ... | no  _ = []
  ... | yes g = x ∷ go (r (f x) (smaller g))

record Is {α} {A : Set α} (x : A) : Set α where
  ¡ = x
open Is

! : ∀ {α} {A : Set α} -> (x : A) -> Is x
! _ = _



_-⁺_ : ∀ {m} -> ℕ -> Is (suc m) -> ℕ
n -⁺ im = n ∸ ¡ im

lem : ∀ {n m} {im : Is (suc m)} -> m < n -> n -⁺ im <′ n
lem {suc n} {m} (s≤s _) = s≤′s (≤⇒≤′ (n∸m≤n m n))

iter-sub : ∀ {m} -> ℕ -> Is (suc m) -> List ℕ
iter-sub n im = calls (λ n -> n -⁺ im) <-well-founded lem (_≤?_ (¡ im)) n

_div⁺_ : ∀ {m} -> ℕ -> Is (suc m) -> ℕ
n div⁺ im = length (iter-sub n im)

_div_ : ℕ -> (m : ℕ) {_ : False (m ≟ 0)} -> ℕ
n div  0      = λ{()}
n div (suc m) = n div⁺ (! (suc m))

test-1 : iter-sub 10 (! 3) ≡ 10 ∷ 7 ∷ 4 ∷ []
test-1 = refl

test-2 : iter-sub 16 (! 4) ≡ 16 ∷ 12 ∷ 8 ∷ 4 ∷ []
test-2 = refl

test-3 : map (λ n -> n div 3)
           (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ [])
         ≡ (0 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ 2 ∷ 2 ∷ 2 ∷ 3 ∷ [])
test-3 = refl
