open import Relation.Binary.PropositionalEquality
open import Data.Unit.Base
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.List.Base

infix 5 _==ᵗ_ _==ᵀ_

data Type : Set where
  unit : Type
  bool : Type
  nat  : Type
  list : Type -> Type

⟦_⟧ : Type -> Set
⟦ unit   ⟧ = ⊤
⟦ bool   ⟧ = Bool
⟦ nat    ⟧ = ℕ
⟦ list a ⟧ = List ⟦ a ⟧

_==ᵗ_ : Type -> Type -> Bool
unit   ==ᵗ unit   = true
bool   ==ᵗ bool   = true
nat    ==ᵗ nat    = true
list a ==ᵗ list b = a ==ᵗ b
_      ==ᵗ _      = false

data Repr : Set -> Set where
  repr : ∀ a -> Repr ⟦ a ⟧

instance
  irepr : ∀ {a} -> Repr ⟦ a ⟧
  irepr = repr _

_==ᵀ_ : ∀ A B {{_ : Repr A}} {{_ : Repr B}} -> Bool
_==ᵀ_ _ _ {{repr a}} {{repr b}} = a ==ᵗ b

test-bool : Bool ==ᵀ Bool ≡ true
test-bool = refl

test-list : List ℕ ==ᵀ List ℕ ≡ true
test-list = refl

test-unit-bool : ⊤ ==ᵀ Bool ≡ false
test-unit-bool = refl
