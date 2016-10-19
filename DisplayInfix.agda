open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Base

record R : Set where
  infixl 6 _⊕_

  field
    _⊕_    : ℕ -> ℕ -> ℕ
    comm-⊕ : ∀ n m -> n ⊕ m ≡ m ⊕ n

private open module Display-⊕ {r} = R r using (_⊕_)
{-# DISPLAY R._⊕_ _ n m = n ⊕ m #-}

flipR : R -> R
flipR r = record
  { _⊕_ = flip (R._⊕_ r)
  -- The type of the hole is `(n m : ℕ) → m ⊕ n ≡ n ⊕ m` after normalization.
  -- It would be `(n m : ℕ) → (r R.⊕ m) n ≡ (r R.⊕ n) m` without the Display pragma.
  ; comm-⊕ = {!!}
  }
