open import Function
open import Relation.Nullary.Decidable
open import Data.Empty
open import Data.Unit.Base
open import Data.Bool.Base hiding (_≟_)
open import Data.Nat.Base
open import Data.List.Base

record Sing {α} {A : Set α} (x : A) : Set where

_==_ : ℕ -> ℕ -> Bool
n == m = ⌊ n ≟ m ⌋

_∈?_ : ℕ -> List ℕ -> Set
n ∈? ns = foldr (λ m r -> if n == m then ⊤ else r) ⊥ ns

remove : ∀ n ns -> n ∈? ns -> List ℕ
remove n  []      ()
remove n (m ∷ ns) p  with n == m
... | true  = ns
... | false = m ∷ remove n ns p

data Kitchen {α} (A : Set α) m is : List ℕ -> Set α where
  stop : ∀ {os} -> Kitchen A m is os
  bake : ∀ {os} -> (Sing m -> Kitchen A (suc m) (m ∷ is) os) -> Kitchen A m is os
  eat  : ∀ {i os} {p : i ∈? is}
       -> Sing i -> Kitchen A m (remove i is p) os -> Kitchen A m is os
  keep : ∀ {i os} {p : i ∈? is}
       -> Sing i -> Kitchen A m (remove i is p) os -> Kitchen A m is (i ∷ os)

postulate Cake : Set

ok : Kitchen Cake 0 [] (_ ∷ _ ∷ [])
ok = bake λ brownie ->
     bake λ muffin  ->
     bake λ cupcake ->
     keep muffin    $
     eat  brownie   $
     keep cupcake   $
     stop

-- {p : ⊥}
unsolved_meta : Kitchen Cake 0 [] (_ ∷ [])
unsolved_meta = bake λ brownie ->
                bake λ muffin  ->
                eat  brownie   $
                keep brownie   $
                stop
