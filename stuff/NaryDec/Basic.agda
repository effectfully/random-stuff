module NaryDec.Basic where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Unit.Base
open import Data.Empty
open import Data.Nat.Base

data DecY {α} (A : Set α) : Set α where
  yes : A -> DecY A
  no  : DecY A

_≤?_ : ℕ -> ℕ -> Set
0     ≤? _     = ⊤
_     ≤? 0     = ⊥
suc n ≤? suc m = n ≤? m

_≢0 : ℕ -> Set
_≢0 = _≤?_ 1

record Is {α} {A : Set α} (x : A) : Set α where

! : ∀ {α} {A : Set α} -> (x : A) -> Is x
! _ = _

IsDecPropEq : ∀ {α} -> Set α -> Set α
IsDecPropEq A = IsDecEquivalence {A = A} _≡_

mkDecPropEq : ∀ {α} {A : Set α} -> Decidable {A = A} _≡_ -> IsDecPropEq A
mkDecPropEq _≟_ = record { isEquivalence = isEquivalence ; _≟_ = _≟_ }
