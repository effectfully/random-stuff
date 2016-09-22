open import Level
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Empty

infix 4 _∉_

mutual
  data UList {α} (A : Set α) : Set α where
    []   : UList A
    cons : ∀ x xs -> x ∉ xs -> UList A

  data _∉_ {α} {A : Set α} (x : A) : UList A -> Set α where
    stop : x ∉ []
    keep : ∀ {y xs} -> x ≢ y -> (p : y ∉ xs) -> x ∉ xs -> x ∉ cons y xs p

data Tag {α} (A : Set α) : Set (suc α) where
  ulist : Tag A
  inn   : {R : Set α} -> A -> R -> Tag A

-- It's positive. Agda just doesn't track polarity of indices.
-- "self-polymorphic recursion"
{-# NO_POSITIVITY_CHECK #-}
data UListInn {α} (A : Set α) : Tag A -> Set α where
  []   : UListInn A ulist
  cons : ∀ x (xs : UListInn A ulist) -> UListInn A (inn x xs) -> UListInn A ulist
  stop : ∀ {x} -> UListInn A (inn x (UListInn A ulist ∋ []))
  keep : ∀ {x y} {xs : UListInn A ulist}
       -> x ≢ y
       -> (p : UListInn A (inn y xs))
       -> UListInn A (inn x xs)
       -> UListInn A (inn x (UListInn.cons y xs p))

mutual
  coeUList : ∀ {α} {A : Set α} -> UList A -> UListInn A ulist
  coeUList  []           = []
  coeUList (cons x xs p) = cons x (coeUList xs) (coeInn p)

  coeInn : ∀ {α} {A : Set α} {x : A} {xs} -> x ∉ xs -> UListInn A (inn x (coeUList xs))
  coeInn  stop        = stop
  coeInn (keep c p q) = keep c (coeInn p) (coeInn q)

mutual
  uncoeUList : ∀ {α} {A : Set α} -> UListInn A ulist -> UList A
  uncoeUList  []           = []
  uncoeUList (cons x xs p) = cons x (uncoeUList xs) (uncoeInn p)

  uncoeInn : ∀ {α} {A : Set α} {x : A} {xs} -> UListInn A (inn x xs) -> x ∉ uncoeUList xs
  uncoeInn  stop        = stop
  uncoeInn (keep c p q) = keep c (uncoeInn p) (uncoeInn q)
