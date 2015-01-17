-- This is related to http://webcache.googleusercontent.com/search?q=cache:CkjO-Ym-CSsJ:comments.gmane.org/gmane.science.mathematics.logic.coq.club/13794+&cd=1&hl=ru&ct=clnk&gl=ru&client=firefox-a
-- and to https://github.com/wjzz/Agda-small-developments-and-examples/blob/master/UnitNotBool.agda

open import Level
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Product
open import Data.Nat as N
open import Data.Fin as F hiding (_≤_)
open import Data.List

≤-trans : ∀ {n m p} -> n ≤ m -> m ≤ p -> n ≤ p
≤-trans  z≤n       _        = z≤n
≤-trans (s≤s le1) (s≤s le2) = s≤s (≤-trans le1 le2)

1+n≰n : ∀ {n} -> N.suc n ≰ n
1+n≰n (s≤s le) = 1+n≰n le

infix 2 _∈_
infixr 5 _u∷_

data _∈_ {α : Level} {A : Set α} : A -> List A -> Set α where
  here  : ∀ {x xs} -> x ∈ x ∷ xs
  there : ∀ {x xs y} -> x ∈ xs -> x ∈ y ∷ xs

_∉_ : {α : Level} {A : Set α} -> A -> List A -> Set α
x ∉ xs = ¬ (x ∈ xs)

data Uniq {α : Level} {A : Set α} : List A -> Set α where
  u[]  : Uniq []
  _u∷_ : ∀ {x xs} -> x ∉ xs -> Uniq xs -> Uniq (x ∷ xs)

uniq-delete-1 : ∀ {α} {A : Set α} {x} {y} {xs : List A} -> Uniq (x ∷ y ∷ xs) -> Uniq (x ∷ xs)
uniq-delete-1 (n u∷ _ u∷ u) = (n ∘ there) u∷ u

lower-list : ∀ {n} -> List (Fin (N.suc n)) -> List (Fin n)
lower-list  []          = []
lower-list (zero  ∷ xs) = lower-list xs
lower-list (suc i ∷ xs) = i ∷ lower-list xs

disappeared : ∀ {n} {i : Fin n} -> ∀ xs -> Uniq (F.suc i ∷ xs) -> i ∉ lower-list xs
disappeared  []           u            ()
disappeared (zero  ∷ xs)  u            ∈xs        = disappeared xs (uniq-delete-1 u) ∈xs
disappeared (suc i ∷ xs) (s-i-∉ u∷ _)  here       = ⊥-elim (s-i-∉ here) 
disappeared (suc i ∷ xs)  u           (there ∈xs) = disappeared xs (uniq-delete-1 u) ∈xs

uniq-lowered : ∀ {n} -> (xs : List (Fin (N.suc n))) -> Uniq xs -> Uniq (lower-list xs)
uniq-lowered  []           u[]        = u[]
uniq-lowered (zero  ∷ xs) (z-∉   u∷ u) = uniq-lowered xs u
uniq-lowered (suc i ∷ xs) (s-i-∉ u∷ u) = disappeared xs (s-i-∉ u∷ u) u∷ uniq-lowered xs u

length-lowered-without-zero : ∀ {p n} -> (xs : List (Fin (N.suc n)))
                            -> F.zero ∉ xs -> length (lower-list xs) ≤ p -> length xs ≤ p
length-lowered-without-zero  []          z-∉  le      = z≤n
length-lowered-without-zero (zero  ∷ xs) z-∉  le      = ⊥-elim (z-∉ here)
length-lowered-without-zero (suc i ∷ xs) z-∉ (s≤s le) =
  s≤s (length-lowered-without-zero xs (z-∉ ∘ there) le)

length-lowered : ∀ {p n} -> (xs : List (Fin (N.suc n)))
               -> Uniq xs -> length (lower-list xs) ≤ p -> length xs ≤ N.suc p
length-lowered  []           u            le      = z≤n
length-lowered (zero  ∷ xs) (z-∉ u∷ _)    le      = 
  s≤s (length-lowered-without-zero xs z-∉ le)
length-lowered (suc i ∷ xs) (s-i-∉ u∷ u) (s≤s le) = s≤s (length-lowered xs u le)

uniq-length : ∀ {n} {xs : List (Fin n)} -> Uniq xs -> length xs ≤ n
uniq-length {0}     {[]}     _ = z≤n
uniq-length {0}     {() ∷ _}
uniq-length {suc n} {xs}     u = length-lowered xs u (uniq-length (uniq-lowered xs u))



simpleEx : ℕ -> List ℕ
simpleEx  0      = 0 ∷ []
simpleEx (suc n) = N.suc n ∷ simpleEx n

∈-simpleEx : ∀ n -> n ∈ simpleEx n
∈-simpleEx  0      = here
∈-simpleEx (suc n) = here

weak-simpleEx : ∀ {m} -> (n : ℕ) -> N.suc m ∈ simpleEx n -> m ∈ simpleEx n
weak-simpleEx  0      (there ())
weak-simpleEx (suc n)  here       = there (∈-simpleEx n)
weak-simpleEx (suc n) (there ∉xs) = there (weak-simpleEx n ∉xs)

∉-simpleEx : ∀ n -> N.suc n ∉ simpleEx n
∉-simpleEx  0      (there ())
∉-simpleEx (suc n) (there ∈xs) = ∉-simpleEx n (weak-simpleEx n ∈xs)

simpleEx-Uniq : ∀ n -> Uniq (simpleEx n)
simpleEx-Uniq  0      = (λ ()) u∷ u[]
simpleEx-Uniq (suc n) = ∉-simpleEx n u∷ simpleEx-Uniq n

simpleEx-length : ∀ n -> length (simpleEx n) > n
simpleEx-length  0      = s≤s z≤n
simpleEx-length (suc n) = s≤s (simpleEx-length n)



Fin-∄ : ∀ {n} -> ∄ λ (xs : List (Fin n)) -> Uniq xs × length xs > n
Fin-∄ (xs , u , le) = 1+n≰n (≤-trans le (uniq-length u))

ℕ-∃ : ∀ {n} -> ∃ λ (xs : List ℕ) -> Uniq xs × length xs > n
ℕ-∃ {n} = simpleEx n , simpleEx-Uniq n , simpleEx-length n 

Fin≢ℕ : ∀ n -> Fin n ≢ ℕ 
Fin≢ℕ n Fin≡ℕ with Fin-∄ {n} 
... | ℕ-∄ rewrite Fin≡ℕ = ℕ-∄ ℕ-∃