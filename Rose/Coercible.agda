open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality
open import Data.List.Base
open import Data.Product

infixr 5 _∷₁_
infixr 4 _,ᵢ_
infixr 2 _×ᵢ_

record Σᵢ {α β} (A : Set α) (B : A -> Set β) : Set (α ⊔ β) where
  constructor _,ᵢ_
  field
    iproj₁  : A
    .iproj₂ : B iproj₁
open Σᵢ

_×ᵢ_ : ∀ {α β} -> Set α -> Set β -> Set (α ⊔ β)
A ×ᵢ B = Σᵢ A λ _ -> B

data List₁ {α β} {A : Set α} (B : A -> Set β) : List A -> Set β where
  []₁  : List₁ B []
  _∷₁_ : ∀ {x xs} -> B x -> List₁ B xs -> List₁ B (x ∷ xs)

map₁ : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : A -> Set γ} {xs}
     -> (∀ {x} -> B x -> C x) -> List₁ B xs -> List₁ C xs
map₁ g  []₁      = []₁
map₁ g (y ∷₁ ys) = g y ∷₁ map₁ g ys

data Somewhere {α β} {A : Set α} (B : A -> Set β) : List A -> Set β where
  here  : ∀ {x xs} -> B x -> Somewhere B (x ∷ xs)
  there : ∀ {x xs} -> Somewhere B xs -> Somewhere B (x ∷ xs)

Cons : ∀ {ι} -> Set ι -> ∀ α -> Set (ι ⊔ lsuc α)
Cons I α = ∃ λ (A : Set α) -> A -> List I × I

Extend : ∀ {ι α β} {I : Set ι} -> (I -> Set β) -> I -> Cons I α -> Set (ι ⊔ α ⊔ β)
Extend F i (A , f) = ∃ λ x -> let is , j = f x in List₁ F is ×ᵢ i ≡ j

mutual
  record Rose {ι α} {I : Set ι} (cs : List (Cons I α)) i : Set (ι ⊔ α) where
    inductive
    constructor rose
    field childs : Childs cs cs i

  Childs : ∀ {ι α} {I : Set ι} -> List (Cons I α) -> List (Cons I α) -> I -> Set (ι ⊔ α)
  Childs cs₁ cs₂ i = Somewhere (Extend (Rose cs₁) i) cs₂

coerceChilds : ∀ {ι α} {I : Set ι} {cs₁ cs₂ : List (Cons I α)} {j i}
             -> (p : j ≡ i) -> Childs cs₁ cs₂ i -> Childs cs₁ cs₂ j
coerceChilds p (here  (x , rs ,ᵢ q)) = here (x , rs ,ᵢ trans p q)
coerceChilds p (there  s)            = there (coerceChilds p s)

coerce : ∀ {ι α} {I : Set ι} {cs : List (Cons I α)} {j i} -> (p : j ≡ i) -> Rose cs i -> Rose cs j
coerce p (rose cs) = rose (coerceChilds p cs)

module Vec where
  open import Function
  open import Data.Unit.Base
  open import Data.Nat.Base

  Vec : ∀ {α} -> Set α -> ℕ -> Set α
  Vec A = Rose ((Lift ⊤ , const ([] , 0)) ∷ ((A × ℕ) , λ p -> proj₂ p ∷ [] , suc (proj₂ p)) ∷ [])

  nil : ∀ {α} {A : Set α} -> Vec A 0
  nil = rose (here (, []₁ ,ᵢ refl))

  cons : ∀ {n α} {A : Set α} -> A -> Vec A n -> Vec A (suc n)
  cons {n} x xs = rose (there (here ((x , n) , xs ∷₁ []₁ ,ᵢ refl)))

  elimVec : ∀ {α π} {A : Set α} {n}
          -> (P : ∀ {n} -> Vec A n -> Set π)
          -> (∀ {n} {xs : Vec A n} x -> P xs -> P (cons x xs))
          -> P nil
          -> (xs : Vec A n)
          -> P xs
  elimVec P f z (rose (here  (_ , []₁ ,ᵢ p)))                    = {!z!}
  elimVec P f z (rose (there (here ((x , n) , xs ∷₁ []₁ ,ᵢ p)))) = {!f x (elimVec P f z xs)!}
  elimVec P f z (rose (there (there ())))
