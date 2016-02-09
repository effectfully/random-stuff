open import Level renaming (zero to lzero; suc to lsuc)
open import Data.List.Base
open import Data.Product

infixr 5 _∷₁_

data List₁ {α β} {A : Set α} (B : A -> Set β) : List A -> Set β where
  []₁  : List₁ B []
  _∷₁_ : ∀ {x xs} -> B x -> List₁ B xs -> List₁ B (x ∷ xs)

data Somewhere {α β} {A : Set α} (B : A -> Set β) : List A -> Set β where
  here  : ∀ {x xs} -> B x -> Somewhere B (x ∷ xs)
  there : ∀ {x xs} -> Somewhere B xs -> Somewhere B (x ∷ xs)

Over : ∀ {ι} -> Set ι -> ∀ α -> Set (ι ⊔ lsuc α)
Over I α = I -> List (Σ (Set α) λ A -> A -> List I)

record Rose {ι α} {I : Set ι} (F : Over I α) i : Set (ι ⊔ α) where
  inductive
  constructor rose
  field childs : Somewhere (uncurry λ A f -> Σ A λ x -> List₁ (Rose F) (f x)) (F i)
  


open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Unit.Base
open import Data.Nat.Base
open import Data.Product

module Nat where
  Nat : Set
  Nat = Rose (λ _ -> (⊤ , λ _ -> []) ∷ (⊤ , λ _ -> tt ∷ []) ∷ []) tt

  z : Nat
  z = rose (here (tt , []₁))

  s : Nat -> Nat
  s n = rose (there (here (tt , (n ∷₁ []₁))))

  elimNat : ∀ {π} -> (P : Nat -> Set π) -> (∀ {n} -> P n -> P (s n)) -> P z -> ∀ n -> P n
  elimNat P f x (rose (here  (tt , []₁)))             = x
  elimNat P f x (rose (there (here (tt , n ∷₁ []₁)))) = f (elimNat P f x n)
  elimNat P f x (rose (there (there ())))

module Vec where
  open Nat

  Vec : ∀ {α} -> Set α -> Nat -> Set α
  Vec A = Rose λ n ->   (Lift (n ≡ z) , λ _ -> [])
                      ∷ ((∃ λ m -> n ≡ s m × A) , λ p -> proj₁ p ∷ [])
                      ∷ []

  nil : ∀ {α} {A : Set α} -> Vec A z
  nil = rose (here (lift refl , []₁))

  cons : ∀ {n α} {A : Set α} -> A -> Vec A n -> Vec A (s n)
  cons x xs = rose (there (here ((, refl , x) , xs ∷₁ []₁)))

  elimVec : ∀ {α π} {A : Set α} {n}
          -> (P : ∀ {n} -> Vec A n -> Set π)
          -> (∀ {n} {xs : Vec A n} x -> P xs -> P (cons x xs))
          -> P nil
          -> (xs : Vec A n)
          -> P xs
  elimVec P f z (rose (here  (lift refl , []₁)))                     = z
  elimVec P f z (rose (there (here ((_ , (refl , x)) , xs ∷₁ []₁)))) = f x (elimVec P f z xs)
  elimVec P f z (rose (there (there ())))
