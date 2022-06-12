{-# OPTIONS --type-in-type #-}  -- Just for convenience, not essential.

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Base

coerce : ∀ {A B} -> A ≡ B -> A -> B
coerce refl = id

record KitRecN : Set where
  field
    RecN : ℕ -> Set
    recN : ∀ n -> RecN n

    Rec0-correct
      : RecN 0
      ≡ ∀ {R} -> (∀ {Q} -> Q -> Q) -> R -> R
    Rec1-correct
      : RecN 1
      ≡ ∀ {A R} -> (∀ {Q} -> (A -> Q) -> Q) -> (A -> R) -> R
    Rec2-correct
      : RecN 2
      ≡ ∀ {A B R} -> (∀ {Q} -> (A -> B -> Q) -> Q) -> (A -> B -> R) -> R
    Rec3-correct
      : RecN 3
      ≡ ∀ {A B C R} -> (∀ {Q} -> (A -> B -> C -> Q) -> Q) -> (A -> B -> C -> R) -> R

    rec0-correct
      : (λ {R} -> coerce Rec0-correct (recN 0) {R})
      ≡ λ k f -> f
    rec1-correct
      : (λ {A R} -> coerce Rec1-correct (recN 1) {A} {R})
      ≡ λ k f -> f (k λ x -> x)
    rec2-correct
      : (λ {A B R} -> coerce Rec2-correct (recN 2) {A} {B} {R})
      ≡ λ k f -> f (k λ x y -> x) (k λ x y -> y)
    rec3-correct
      : (λ {A B C R} -> coerce Rec3-correct (recN 3) {A} {B} {C} {R})
      ≡ λ k f -> f (k λ x y z -> x) (k λ x y z -> y) (k λ x y z -> z)

postulate
  kitRecN : KitRecN
