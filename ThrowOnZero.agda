open import Reflection
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit.Base
open import Data.Nat.Base
open import Data.List.Base

_`div-suc`_ : ℕ -> ℕ -> ℕ
n `div-suc` m = go n m where
  go : ℕ -> ℕ -> ℕ
  go  0       m      = 0
  go (suc n)  0      = suc (go n m)
  go (suc n) (suc m) = go n m

throwOnZero : ℕ -> Term -> TC ⊤
throwOnZero zero _    = typeError (strErr "A divisor can't be zero" ∷ [])
throwOnZero _    hole = bindTC (quoteTC tt) (unify hole)

_≢0 : ℕ -> Set
_≢0 0 = ⊥
_≢0 _ = ⊤

_`div`_ : ℕ -> ∀ m {@(tactic throwOnZero m) _ : m ≢0} -> ℕ
_`div`_ n  zero   {()}
_`div`_ n (suc m)      = n `div-suc` m

_ : map (λ n -> n `div` 3) (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ 11 ∷ 12 ∷ [])
  ≡                        (0 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ 2 ∷ 2 ∷ 2 ∷ 3 ∷ 3  ∷ 3  ∷ 4  ∷ [])
_ = refl

-- A divisor can't be zero
-- when checking that 0 is a valid argument to a function of type
-- (m : ℕ) {@(tactic throwOnZero m) _ : m ≢0} → ℕ
_ : ∀ n -> n `div` 0 ≡ n `div` 0
_ = λ n -> refl
