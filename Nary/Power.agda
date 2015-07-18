module Nary.Power where

open import Level         hiding (suc)
open import Function
open import Data.Unit.Base
open import Data.Nat.Base hiding (_⊔_)
open import Data.Product
open import Data.Vec

infixl 6 _^_
infixl 6 _⊔ⁿ_

_^_ : ∀ {α} -> Set α -> ℕ -> Set α
A ^ 0     = Lift ⊤
A ^ suc n = A × A ^ n

to-^ : ∀ {n α} {A : Set α} -> Vec A n -> A ^ n
to-^ = foldr (_^_ _) _,_ _

from-^ : ∀ {n α} {A : Set α} -> A ^ n -> Vec A n
from-^ {0}      _       = []
from-^ {suc _} (x , xs) = x ∷ from-^ xs

on-^ : ∀ {α β n} {A : Set α} {B : Vec A n -> Set β}
     -> (∀ xs -> B xs) -> ∀ xs -> B (from-^ xs)
on-^ f = f ∘ from-^

mono-^ : ∀ {α n m} {A : Set α} -> (Vec A n -> Vec A m) -> A ^ n -> A ^ m
mono-^ f = to-^ ∘ on-^ f

_⊔ⁿ_ : ∀ {n} -> Level ^ n -> Level -> Level
_⊔ⁿ_ = on-^ $ flip $ foldr _ _⊔_
