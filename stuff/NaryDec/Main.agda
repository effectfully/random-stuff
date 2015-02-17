module NaryDec.Main where

open import Level as Le using (Level)
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Base
open import Data.Product

open import NaryDec.Basic public
open import NaryDec.Nary

Of-form₁ : ∀ n {β} {αs : Level ^ n} {As : Sets αs} {B : Set β} -> B -> (As ->ⁿ B) -> Set _
Of-form₁ n y f = ∃ⁿ n (compⁿ n (_≡_ y) f)

Of-form₂ : ∀ n m {γ} {αs : Level ^ n} {βs : Level ^ m}
           {As : Sets αs} {Bs : Sets βs} {C : Set γ}
         -> C -> (As ->ⁿ Bs ->ⁿ C) -> Set _
Of-form₂ n m z f = Of-form₁ (n + m) z (uncurryⁿ² n f)

Dec-Of-form₁ : ∀ n {β} {αs : Level ^ n} {As : Sets αs} {B : Set β} -> (As ->ⁿ B) -> Set _
Dec-Of-form₁ n f = ∀ y -> DecY (Of-form₁ n y f)

Dec-Of-form₂ : ∀ n m {γ} {αs : Level ^ n} {βs : Level ^ m}
               {As : Sets αs} {Bs : Sets βs} {C : Set γ}
             -> (As ->ⁿ Bs ->ⁿ C) -> Set _
Dec-Of-form₂ n m f = ∀ z -> DecY (Of-form₂ n m z f)

lookup : ∀ n {n' α β} {αs : Level ^ n} {αs' : Level ^ n'}
         {As : Sets αs} {A : Set α} {As' : Sets αs'} {B : Set β}
         {f : As ->ⁿ (A -> As' ->ⁿ B)} {y : B}
       -> Of-form₂ n (suc n') y f -> A
lookup  0      (x , p) = x
lookup (suc n) (x , p) = lookup n p

comp : ∀ n {m β γ} {αs : Level ^ n} {βs : Level ^ m}
       {As : Sets αs} {B : Set β} {Bs : Sets βs} {C : Set γ}
       {g : B -> Bs ->ⁿ C} {f : As ->ⁿ B} {y : B} {z : C}
     -> Of-form₁ n   y  f
     -> Of-form₁ m   z (g y)
     -> Of-form₂ n m z (compⁿ n g f)
comp  0       refl   r = r
comp (suc n) (x , q) r = x , comp n q r

inject : ∀ m {n p γ δ} {αs : Level ^ n} {βs : Level ^ m} {γs : Level ^ p}
         {As : Sets αs} {Bs : Sets βs} {C : Set γ} {Cs : Sets γs} {D : Set δ}
         {g : Bs ->ⁿ (C -> Cs ->ⁿ D)} {f : As ->ⁿ C} {z : D}
       -> (q : Of-form₂  m      (suc p)  z            g)
       ->      Of-form₁  n              (lookup m q)  f
       ->      Of-form₂ (m + n)  p       z           (compⁿ² m n g f)
inject  0  {n} (_ , q) r = comp n r q
inject (suc m) (x , q) r = x , inject m q r

extend₀ : ∀ m p n {γ δ} {αs : Level ^ n} {βs : Level ^ m} {γs : Level ^ p}
          {As : Sets αs} {Bs : Sets βs} {C : Set γ} {Cs : Sets γs} {D : Set δ}
          {g : Bs ->ⁿ (C -> Cs ->ⁿ D)} {f : As ->ⁿ C}
        -> Dec-Of-form₂  m      (suc p)  g
        -> Dec-Of-form₁  n               f
        -> Dec-Of-form₂ (m + n)  p      (compⁿ² m n g f)
extend₀ m _ n g f z with g z
... | no    = no
... | yes q with f (lookup m q)
... | no    = no
... | yes r = yes (inject m q r)

reduce : ∀ n {m β γ} {αs : Level ^ n} {βs : Level ^ m}
         {As : Sets αs} {B : Set β} {Bs : Sets βs} {C : Set γ}
         {f : As ->ⁿ (B -> Bs ->ⁿ C)} {z : C}
       -> (q : Of-form₂ n (suc m) z  f)
       ->      Of-form₂ n  m      z (applyⁿ n f (lookup n q))
reduce  0      (_ , q) = q
reduce (suc n) (x , q) = x , reduce n q

module _ where
  open import Relation.Nullary
  open module IsDecPropEqI {α} {A : Set α} {{idpe : IsDecPropEq A}} = IsDecEquivalence idpe

  bound₀ : ∀ n m {β γ} {αs : Level ^ n} {βs : Level ^ m}
           {As : Sets αs} {B : Set β} {Bs : Sets βs} {C : Set γ}
           {f : As ->ⁿ (B -> Bs ->ⁿ C)} {{idpe : IsDecPropEq B}}
         -> Dec-Of-form₂ n (suc m)  f
         -> (y : B)
         -> Dec-Of-form₂ n  m      (applyⁿ n f y)
  bound₀ n m f y z with f z
  ... | no    = no
  ... | yes q with y ≟ lookup n q
  ... | no  _ = no
  ... | yes r rewrite r = yes (reduce n q)

-- Not sure, whether (pred m + (p ∸ m) + n) should be simplified to (pred p + n) or not.
-- Would it affect unification, when `n', `m' or `p' are universally quantified,
-- in a desirable or undesirable way? 
extend = λ m {p} {n} {_ : 1 ≤? m} {_ : m ≤? p}
           {γ} {δ} {αs} {βs} {γs} {As} {Bs} {C} {Cs} {D} {g} {f}
           (dg : Is p × _) (df : Is n × _)
         -> ! (pred m + (p ∸ m) + n) , extend₀ (pred m) (p ∸ m) n
                {γ} {δ} {αs} {βs} {γs} {As} {Bs} {C} {Cs} {D} {g} {f}
                (proj₂ dg) (proj₂ df)

bound = λ n {_ : 1 ≤? n} {m} {β} {γ} {αs} {βs} {As} {B} {Bs} {C} {f}
          {{idpe}} (df : Is m × _) y
        -> ! (pred m) , bound₀ (pred n) (m ∸ n) {β} {γ} {αs} {βs} {As} {B} {Bs} {C} {f}
               {{idpe}} (proj₂ df) y

Dec-Of-form : ∀ n {β} {αs : Level ^ n} {As : Sets αs} {B : Set β} -> (As ->ⁿ B) -> Set _
Dec-Of-form n f = Is n × Dec-Of-form₁ n f
