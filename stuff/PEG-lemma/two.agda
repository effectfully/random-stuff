open import Data.List
open import Data.Fin hiding (_+_)
open import Data.Nat renaming (ℕ to Nat)
open import Data.Product as P
open import Data.Vec using (Vec ; lookup)
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _==_ ; sym to symm) hiding (inspect)
open import Data.Maybe as Maybe
open import Function

postulate A : Set

data Foo : Nat -> Set where
  emp : forall {n} -> Foo n
  sym : forall {n} -> A -> Foo n
  var : forall {n} -> Fin (suc n) -> Foo n
  _o_ : forall {n} -> Foo n -> Foo n -> Foo n
 
Con : Nat -> Set
Con n = Vec (Foo n) (suc n)

infix 1 _::_=>_

data _::_=>_ {n} (G : Con n) : Foo n × List A -> Maybe (List A) -> Set where
  empty       : ∀ {x}     -> G :: emp   ,  x      => just []
  sym-success : ∀ {a x}   -> G :: sym a , (a ∷ x) => just (a ∷ [])
  sym-failure : ∀ {a b x} -> ¬ (a == b) -> G :: sym a , b ∷ x => nothing
  var         : ∀ {x o} {v : Fin (suc n)} -> G :: lookup v G , x => o -> G :: var v , x => o
  o-success : ∀ {e e' x x' y}
            -> G :: e      , x ++ x' ++ y => just  x
            -> G :: e'     ,      x' ++ y => just  x'
            -> G :: e o e' , x ++ x' ++ y => just (x ++ x')
  o-fail1   : ∀ {e e' z}
            -> G :: e      , z => nothing
            -> G :: e o e' , z => nothing
  o-fail2   : ∀ {e e' x z}
            -> G :: e      , x ++ z => just x
            -> G :: e'     ,      z => nothing
            -> G :: e o e' , x ++ z => nothing

postulate
  cut : ∀ {α} {A : Set α} -> ∀ xs {ys zs : List A} -> xs ++ ys == xs ++ zs -> ys == zs

open Deprecated-inspect

un-just : ∀ {α} {A : Set α} {x y : A} -> _==_ {A = Maybe A} (just x) (just y) -> x == y
un-just refl = refl

lemma : ∀ {n} {G : Con n} {f x p p'} -> G :: f , x => p -> G :: f , x => p' -> p == p'
lemma  empty                                empty                = refl
lemma  sym-success                          sym-success          = refl
lemma  sym-success                         (sym-failure p)       = ⊥-elim (p refl)
lemma (sym-failure p)                       sym-success          = ⊥-elim (p refl)
lemma (sym-failure _)                      (sym-failure _)       = refl
lemma (var pr1)                            (var pr2)             = lemma pr1 pr2
lemma (o-success {x = x} {x'} {y} pr1 pr2)  pr3                  with inspect (x ++ x' ++ y)
... | z with-≡ r rewrite r with z | pr3
... | ._ | o-success {x = x''} pr1' pr2'
  rewrite un-just (lemma pr1 pr1') | cut x'' r | un-just (lemma pr2 pr2') = refl
... | ._ | o-fail1             pr1'                              = case lemma pr1 pr1' of λ()
... | ._ | o-fail2   {x = x''} pr1' pr2'
  rewrite un-just (lemma pr1 pr1') | cut x'' r                   = case lemma pr2 pr2' of λ()
lemma (o-fail1   pr1)                      (o-success pr1' pr2') = case lemma pr1 pr1' of λ()
lemma (o-fail1   pr1)                      (o-fail1   pr1')      = refl
lemma (o-fail1   pr1)                      (o-fail2   pr1' pr2') = refl
lemma (o-fail2 {x = x} {y} pr1 pr2)         pr3                  with inspect (x ++ y)
... | z with-≡ r rewrite r with z | pr3 
... | ._ | o-success {x = x''} pr1' pr2'
  rewrite (un-just (lemma pr1 pr1')) | cut x'' r                 = case lemma pr2 pr2' of λ()
... | ._ | o-fail1             pr1'                              = refl
... | ._ | o-fail2             pr1' pr2'                         = refl
