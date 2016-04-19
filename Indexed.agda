{-# OPTIONS --type-in-type #-}

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Empty

Indexed : Set -> Set
Indexed I = (I -> Set) -> I -> Set

data IWer {I} (Ψ : Indexed I) : I -> Set where
  call : ∀ {S i} -> Ψ S i -> (∀ {i′} -> S i′ -> IWer Ψ i′) -> IWer Ψ i

fmap : ∀ {I i} {Ψ Φ : Indexed I} -> (∀ {S i} -> Ψ S i -> Φ S i) -> IWer Ψ i -> IWer Φ i
fmap f (call a k) = call (f a) (λ x -> fmap f (k x))



open import Data.Nat.Base
open import Data.List.Base hiding ([]; _∷_; foldr)

data VecF (A : Set) : Indexed ℕ where
  Nil  : VecF A (const ⊥) 0
  Cons : ∀ {n} -> A -> VecF A (n ≡_) (suc n)

Vec : Set -> ℕ -> Set
Vec = IWer ∘ VecF

[] : ∀ {A} -> Vec A 0
[] = call Nil (λ())

infixr 5 _∷_
_∷_ : ∀ {n A} -> A -> Vec A n -> Vec A (suc n)
x ∷ xs = call (Cons x) (λ q -> subst (Vec _) q xs)

-- Nope.
-- elimVec : ∀ {n A}
--         -> (P : ∀ {n} -> Vec A n -> Set)
--         -> (∀ {n} {xs : Vec A n} x -> P xs -> P (x ∷ xs))
--         -> P []
--         -> (xs : Vec A n)
--         -> P xs
-- elimVec P f z (call  Nil     k) = {!z!}
-- elimVec P f z (call (Cons x) k) = {!f x (elimVec P f z (k refl))!}

onVec : ∀ {A B S i} -> (A -> B) -> VecF A S i -> VecF B S i
onVec f  Nil     = Nil
onVec f (Cons x) = Cons (f x)

foldr : ∀ {A n}
      -> (B : ℕ -> Set)
      -> (∀ {n} -> A -> B n -> B (suc n))
      -> B 0
      -> Vec A n
      -> B n
foldr B f z (call  Nil     k) = z
foldr B f z (call (Cons x) k) = f x (foldr B f z (k refl))

toList : ∀ {A n} -> Vec A n -> List A
toList = foldr _ List._∷_ List.[]

test : toList (fmap (onVec suc) (1 ∷ 2 ∷ 3 ∷ [])) ≡ toList (2 ∷ 3 ∷ 4 ∷ [])
test = refl
