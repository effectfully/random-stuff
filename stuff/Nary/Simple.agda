module Nary.Simple where

open import Level         renaming (zero to lzero; suc to lsuc)
open import Function
open import Data.Unit.Base
open import Data.Nat.Base
open import Data.Product  hiding (map)
open import Data.Vec

open import Nary.Power

infixr 0 _->ⁿ_

Sets : ∀ {n} -> (αs : Level ^ n) -> Set (mono-^ (map lsuc) αs ⊔ⁿ lzero)
Sets {0}      _       = ⊤
Sets {suc _} (α , αs) = Σ (Set α) λ A -> A -> Sets αs

_->ⁿ_ : ∀ {n} {αs : Level ^ n} {β} -> Sets αs -> Set β -> Set (αs ⊔ⁿ β)
_->ⁿ_ {0}      _      B = B
_->ⁿ_ {suc _} (_ , F) B = ∀ x -> F x ->ⁿ B


