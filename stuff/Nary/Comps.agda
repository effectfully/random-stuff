module Nary.Comps where

open import Level
open import Function
open import Data.Nat.Base
open import Data.Product

open import Nary.Power

module comp1 where
  open import Data.Vec.N-ary

  compⁿ : ∀ n {α β γ} {X : Set α} {Y : Set β} {Z : Set γ}
        -> (Y -> Z) -> N-ary n X Y -> N-ary n X Z
  compⁿ  0      g y = g y
  compⁿ (suc n) g f = compⁿ n g ∘ f

module comp2 where
  open import Data.Vec.N-ary

  compⁿᵀ : ∀ n {α β γ} {X : Set α} {Y : Set β}
         -> (Y -> Set γ) -> N-ary n X Y -> Set (N-ary-level α γ n)
  compⁿᵀ  0      Z y = Z y
  compⁿᵀ (suc n) Z f = ∀ x -> compⁿᵀ n Z (f x)

  compⁿ : ∀ n {α β γ} {X : Set α} {Y : Set β} {Z : Y -> Set γ}
        -> ((y : Y) -> Z y) -> (f : N-ary n X Y) -> compⁿᵀ n Z f
  compⁿ  0      g y = g y
  compⁿ (suc n) g f = compⁿ n g ∘ f

module comp3 where
  open import Nary.Naive

  compⁿ : ∀ n {Xs : Set ^ n} {Y Z : Set}
        -> (Y -> Z) -> (Xs ->ⁿ Y) -> Xs ->ⁿ Z
  compⁿ  0      g y = g y
  compⁿ (suc n) g f = compⁿ n g ∘ f

module comp4 where
  open import Nary.Naive

  compⁿᵀ : ∀ n {Xs : Set ^ n} {Y : Set}
         -> (Y -> Set) -> (Xs ->ⁿ Y) -> Set
  compⁿᵀ  0      Z y = Z y
  compⁿᵀ (suc n) Z f = ∀ x -> compⁿᵀ n Z (f x)

  compⁿ : ∀ n {Xs : Set ^ n} {Y : Set} {Z : Y -> Set}
        -> ((y : Y) -> Z y) -> (f : Xs ->ⁿ Y) -> compⁿᵀ n Z f
  compⁿ  0      g y = g y
  compⁿ (suc n) g f = compⁿ n g ∘ f

module comp5 where
  open import Nary.Simple

  compⁿ : ∀ n {β γ} {αs : Level ^ n} {Xs : Sets αs} {Y : Set β} {Z : Set γ}
        -> (Y -> Z) -> (Xs ->ⁿ Y) -> Xs ->ⁿ Z
  compⁿ  0      g y = g y
  compⁿ (suc n) g f = compⁿ n g ∘ f

module comp6 where
  open import Nary.Simple

  compⁿᵀ : ∀ n {αs : Level ^ n} {β γ} {Xs : Sets αs} {Y : Set β}
         -> (Y -> Set γ) -> (Xs ->ⁿ Y) -> Set (αs ⊔ⁿ γ)
  compⁿᵀ  0      Z y = Z y
  compⁿᵀ (suc n) Z f = ∀ x -> compⁿᵀ n Z (f x)

  compⁿ : ∀ n {β γ} {αs : Level ^ n} {Xs : Sets αs} {Y : Set β} {Z : Y -> Set γ}
        -> ((y : Y) -> Z y) -> (f : Xs ->ⁿ Y) -> compⁿᵀ n Z f
  compⁿ  0      g y = g y
  compⁿ (suc n) g f = compⁿ n g ∘ f

module comp7 where
  open import Nary.Dependent

  compⁿ : ∀ n {α β γ} {αs : Level ^ n} {Xs : Sets αs α} {Y : Set β} {Z : Set γ}
        -> (Y -> Z) -> (Xs ->ⁿ Y) -> Xs ->ⁿ Z
  compⁿ  0      g f = g ∘ f
  compⁿ (suc n) g f = compⁿ n g ∘ f

module comp8 where
  open import Nary.Dependent
  
  compⁿᵀ : ∀ n {αs : Level ^ n} {β γ} {Xs : Sets αs β}
         -> (Xs ⋯>ⁿ Set γ) -> Fold Xs -> Set (αs ⊔ⁿ γ)
  compⁿᵀ  0      Z y = Z y
  compⁿᵀ (suc n) Z f = ∀ x -> compⁿᵀ n Z (f x)
  
  compⁿ : ∀ n {β γ} {αs : Level ^ n} {Xs : Sets αs β} {Z : Xs ⋯>ⁿ Set γ}
        -> Πⁿ Xs Z -> (f : Fold Xs) -> compⁿᵀ n Z f
  compⁿ  0      g y = g y
  compⁿ (suc n) g f = compⁿ n g ∘ f
