module Nary.Naive where

open import Data.Nat.Base
open import Data.Product

open import Nary.Power

_->ⁿ_ : ∀ {n} -> Set ^ n -> Set -> Set
_->ⁿ_ {0}      _      B = B
_->ⁿ_ {suc _} (A , R) B = A -> (R ->ⁿ B)
