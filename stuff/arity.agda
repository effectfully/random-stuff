open import Function
open import Data.Bool
open import Data.Nat
open import Data.List
open import Reflection

toℕ : Bool -> ℕ
toℕ true  = 1
toℕ false = 0

isVisible : Visibility -> Bool
isVisible visible = true
isVisible _       = false

isVisibleArg : ∀ {A} -> Arg A -> Bool
isVisibleArg (arg (arg-info v _) _) = isVisible v

arityType : Type -> ℕ
arityType (el s (pi σ τ)) = toℕ (isVisibleArg σ) + arityType τ
arityType  _              = 0

arityName : Name -> ℕ
arityName = arityType ∘ type

arityTerm : Term -> ℕ
arityTerm (con c as)      = arityName c ∸ length (filter isVisibleArg as)
arityTerm (def f as)      = arityName f ∸ length (filter isVisibleArg as)
arityTerm (lam v t)       = toℕ (isVisible v) + arityTerm t
arityTerm (pat-lam cs as) = something where postulate something : _
arityTerm  _              = 0

open import Relation.Binary.PropositionalEquality

test-1 : arityTerm (quoteTerm suc) ≡ 1
test-1 = refl

test-1' : arityName (quote suc) ≡ 1
test-1' = refl

test-2 : arityTerm (quoteTerm (zipWith _+_)) ≡ 2
test-2 = refl

test-3 : arityTerm (quoteTerm (λ {α} A -> _∷_ {α} {A})) ≡ 3
test-3 = refl
