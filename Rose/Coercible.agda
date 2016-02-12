open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_])
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

open import Function
open import Data.Unit.Base
open import Data.Bool.Base
open import Data.Nat.Base

module Vec1 where
  Vec : ∀ {α} -> Set α -> ℕ -> Set α
  Vec A = Rose ((Lift ⊤ , const ([] , 0)) ∷ ((A × ℕ) , λ p -> proj₂ p ∷ [] , suc (proj₂ p)) ∷ [])

  nil : ∀ {m α} {A : Set α} -> .(m ≡ 0) -> Vec A m
  nil p = rose (here (, []₁ ,ᵢ p))

  cons : ∀ {n m α} {A : Set α} -> .(m ≡ suc n) -> A -> Vec A n -> Vec A m
  cons {n} p x xs = rose (there (here ((x , n) , xs ∷₁ []₁ ,ᵢ p)))

  []ᵥ : ∀ {α} {A : Set α} -> Vec A 0
  []ᵥ = nil refl

  _∷ᵥ_ : ∀ {n α} {A : Set α} -> A -> Vec A n -> Vec A (suc n)
  _∷ᵥ_ = cons refl

  elimVec : ∀ {n α π} {A : Set α}
          -> (P : ∀ {n} -> Vec A n -> Set π)
          -> (∀ {n m} {xs : Vec A n} -> .(p : m ≡ suc n) -> (x : A) -> P xs -> P (cons p x xs))
          -> (∀ {m} -> .(p : m ≡ 0) -> P (nil p))
          -> (xs : Vec A n)
          -> P xs
  elimVec P f z (rose (here  (_ , []₁ ,ᵢ p)))                    = z p
  elimVec P f z (rose (there (here ((x , n) , xs ∷₁ []₁ ,ᵢ p)))) = f p x (elimVec P f z xs)
  elimVec P f z (rose (there (there ())))

module Vec2 where
  caseℕ : ∀ {α} {A : Set α} -> A -> (ℕ -> A) -> ℕ -> A
  caseℕ x f  0      = x
  caseℕ x f (suc n) = f n

  Vec : ∀ {α} -> Set α -> ℕ -> Set α
  Vec A = Rose (((Σ ℕ (caseℕ (Lift ⊤) (const A))) , uncurry λ n _ -> caseℕ [] [_] n , n) ∷ [])

  nil : ∀ {m α} {A : Set α} -> .(m ≡ 0) -> Vec A m
  nil p = rose (here ((0 , _) , []₁ ,ᵢ p))

  cons : ∀ {n m α} {A : Set α} -> .(m ≡ suc n) -> A -> Vec A n -> Vec A m
  cons {n} p x xs = rose (here ((suc n , x) , xs ∷₁ []₁ ,ᵢ p))

  []ᵥ : ∀ {α} {A : Set α} -> Vec A 0
  []ᵥ = nil refl

  _∷ᵥ_ : ∀ {n α} {A : Set α} -> A -> Vec A n -> Vec A (suc n)
  _∷ᵥ_ = cons refl

  elimVec : ∀ {n α π} {A : Set α}
          -> (P : ∀ {n} -> Vec A n -> Set π)
          -> (∀ {n m} {xs : Vec A n} -> .(p : m ≡ suc n) -> (x : A) -> P xs -> P (cons p x xs))
          -> (∀ {m} -> .(p : m ≡ 0) -> P (nil p))
          -> (xs : Vec A n)
          -> P xs
  elimVec P f z (rose (here ((zero  , _) , []₁       ,ᵢ p))) = z p
  elimVec P f z (rose (here ((suc n , x) , xs ∷₁ []₁ ,ᵢ p))) = f p x (elimVec P f z xs)
  elimVec P f z (rose (there ()))
