module NaryDec.Examples where

open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Nat hiding (_≤?_) renaming (_≟_ to _≟ℕ_)
open import Data.Product
open import Data.Vec

open import NaryDec.Main

dec-suc : Dec-Of-form 1 suc 
dec-suc = , λ{ 0 -> no ; (suc _) -> yes (, refl) }

dec-2+ : Dec-Of-form 1 (_+_ 2)
dec-2+ = extend 1 dec-suc dec-suc

dec-n+ : ∀ n -> Dec-Of-form 1 (_+_ n)
dec-n+  0      = , λ _ -> yes (, refl)
dec-n+ (suc n) = extend 1 dec-suc (dec-n+ n)

data Foo : Set₁ where
  foo : ∀ n -> Vec Set n -> Foo

dec-foo : Dec-Of-form 2 foo
dec-foo = , λ{ (foo _ _) -> yes (, , refl) }

instance
  isDecPropEq-ℕ : IsDecPropEq ℕ
  isDecPropEq-ℕ = mkDecPropEq _≟ℕ_

dec-2 : Dec-Of-form 0 2
dec-2 = bound 1 dec-2+ 0
