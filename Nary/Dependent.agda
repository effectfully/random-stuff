module Nary.Dependent where

open import Level         renaming (zero to lzero; suc to lsuc)
open import Function
open import Data.Unit.Base
open import Data.Nat.Base hiding (_⊔_)
open import Data.Product  hiding (map)
open import Data.Vec

open import Nary.Power

infixr 0 _->ⁿ_ _⋯>ⁿ_

Sets : ∀ {n} -> (αs : Level ^ n) -> ∀ β -> Set (mono-^ (map lsuc) αs ⊔ⁿ lsuc β)
Sets {0}      _       β = Set β
Sets {suc _} (α , αs) β = Σ (Set α) λ X -> X -> Sets αs β

Fold : ∀ {n} {αs : Level ^ n} {β} -> Sets αs β -> Set (αs ⊔ⁿ β)
Fold {0}      Y      = Y
Fold {suc _} (_ , F) = ∀ x -> Fold (F x)

_->ⁿ_ : ∀ {n} {αs : Level ^ n} {β γ}
      -> Sets αs β -> Set γ -> Set (αs ⊔ⁿ β ⊔ γ)
_->ⁿ_ {0}      Y      Z = Y -> Z
_->ⁿ_ {suc _} (_ , F) Z = ∀ x -> F x ->ⁿ Z

_⋯>ⁿ_ : ∀ {n} {αs : Level ^ n} {β γ}
      -> Sets αs β -> Set γ -> Set (αs ⊔ⁿ β ⊔ γ)
_⋯>ⁿ_ {0}      Y      Z = Y -> Z
_⋯>ⁿ_ {suc _} (_ , F) Z = ∀ {x} -> F x ⋯>ⁿ Z

Πⁿ : ∀ {n} {αs : Level ^ n} {β γ}
   -> (Xs : Sets αs β) -> (Xs ⋯>ⁿ Set γ) -> Set (αs ⊔ⁿ β ⊔ γ)
Πⁿ {0}      Y      Z = (y : Y) -> Z y
Πⁿ {suc _} (_ , F) Z = ∀ {x} -> Πⁿ (F x) Z
