module Nary.Comps where

open import Level
open import Data.Nat.Base
open import Data.Product

open import Nary.Power

module comp1 where
  open import Data.Vec.N-ary

  comp : ∀ n {α β γ} {X : Set α} {Y : Set β} {Z : Set γ}
       -> (Y -> Z) -> N-ary n X Y -> N-ary n X Z
  comp  0      g y = g y
  comp (suc n) g f = λ x -> comp n g (f x)

module comp2 where
  open import Data.Vec.N-ary

  Comp : ∀ n {α β γ} {X : Set α} {Y : Set β}
       -> (Y -> Set γ) -> N-ary n X Y -> Set (N-ary-level α γ n)
  Comp  0      Z y = Z y
  Comp (suc n) Z f = ∀ x -> Comp n Z (f x)

  comp : ∀ n {α β γ} {X : Set α} {Y : Set β} {Z : Y -> Set γ}
       -> ((y : Y) -> Z y) -> (f : N-ary n X Y) -> Comp n Z f
  comp  0      g y = g y
  comp (suc n) g f = λ x -> comp n g (f x)

module comp3 where
  open import Nary.Naive

  comp : ∀ n {Xs : Set ^ n} {Y Z : Set}
       -> (Y -> Z) -> (Xs ->ⁿ Y) -> Xs ->ⁿ Z
  comp  0      g y = g y
  comp (suc n) g f = λ x -> comp n g (f x)

module comp4 where
  open import Nary.Naive

  Comp : ∀ n {Xs : Set ^ n} {Y : Set}
       -> (Y -> Set) -> (Xs ->ⁿ Y) -> Set
  Comp  0      Z y = Z y
  Comp (suc n) Z f = ∀ x -> Comp n Z (f x)

  comp : ∀ n {Xs : Set ^ n} {Y : Set} {Z : Y -> Set}
       -> ((y : Y) -> Z y) -> (f : Xs ->ⁿ Y) -> Comp n Z f
  comp  0      g y = g y
  comp (suc n) g f = λ x -> comp n g (f x)

module comp5 where
  open import Nary.Simple

  comp : ∀ n {β γ} {αs : Level ^ n} {Xs : Sets αs} {Y : Set β} {Z : Set γ}
       -> (Y -> Z) -> (Xs ->ⁿ Y) -> Xs ->ⁿ Z
  comp  0      g y = g y
  comp (suc n) g f = λ x -> comp n g (f x)

module comp6 where
  open import Nary.Simple

  Comp : ∀ n {αs : Level ^ n} {β γ} {Xs : Sets αs} {Y : Set β}
       -> (Y -> Set γ) -> (Xs ->ⁿ Y) -> Set (αs ⊔ⁿ γ)
  Comp  0      Z y = Z y
  Comp (suc n) Z f = ∀ x -> Comp n Z (f x)

  comp : ∀ n {β γ} {αs : Level ^ n} {Xs : Sets αs} {Y : Set β} {Z : Y -> Set γ}
       -> ((y : Y) -> Z y) -> (f : Xs ->ⁿ Y) -> Comp n Z f
  comp  0      g y = g y
  comp (suc n) g f = λ x -> comp n g (f x)

module comp7 where
  open import Nary.Dependent

  comp : ∀ n {α β γ} {αs : Level ^ n} {Xs : Sets αs α} {Y : Set β} {Z : Set γ}
       -> (Y -> Z) -> (Xs ->ⁿ Y) -> Xs ->ⁿ Z
  comp  0      g f = λ x -> g (f x)
  comp (suc n) g f = λ x -> comp n g (f x)

module comp8 where
  open import Nary.Dependent
  
  Comp : ∀ n {αs : Level ^ n} {β γ} {Xs : Sets αs β}
       -> (Xs ⋯>ⁿ Set γ) -> Fold Xs -> Set (αs ⊔ⁿ γ)
  Comp  0      Z y = Z y
  Comp (suc n) Z f = ∀ x -> Comp n Z (f x)
  
  comp : ∀ n {β γ} {αs : Level ^ n} {Xs : Sets αs β} {Z : Xs ⋯>ⁿ Set γ}
       -> Πⁿ Xs Z -> (f : Fold Xs) -> Comp n Z f
  comp  0      g y = g y
  comp (suc n) g f = λ x -> comp n g (f x)

  module tests where
    open import Data.Bool
    open import Data.Vec
    open import Relation.Binary.PropositionalEquality

    length : ∀ {α} {A : Set α} {n} -> Vec A n -> ℕ
    length {n = n} _ = n
    
    explicit-replicate : (A : Set) -> (n : ℕ) -> A -> Vec A n
    explicit-replicate _ _ x = replicate x

    foo : (A : Set) -> ℕ -> A -> ℕ
    foo = comp 3 length explicit-replicate

    test : foo Bool 5 true ≡ 5
    test = refl

    foo' : ∀ {α} {A : Set α} -> ℕ -> A -> ℕ
    foo' = comp 2 length (λ n -> replicate {n = n})

    test' : foo' 5 true ≡ 5
    test' = refl

    explicit-replicate' : ∀ α -> (A : Set α) -> (n : ℕ) -> A -> Vec A n
    explicit-replicate' _ _ _ x = replicate x

    -- ... because this would result in an invalid use of Setω ...
    -- error : ∀ α -> (A : Set α) -> ℕ -> A -> ℕ
    -- error = comp 4 length explicit-replicate'
