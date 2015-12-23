module Prelude where

open import Level renaming (zero to lzero; suc to lsuc) public
open import Function public
open import Relation.Binary.PropositionalEquality hiding ([_]) public
open import Data.Nat.Base hiding (_⊔_) public
open import Data.Fin using (Fin; zero; suc) public
open import Data.Sum       renaming (map to smap) public
open import Data.Product   renaming (map to pmap) hiding (,_)  public
open import Data.Vec       renaming (map to vmap) hiding (_∈_; _>>=_; zip) public

infix 4 ,_

pattern ,_ y = _ , y

data ⊥ {α} : Set α where
record ⊤ {α} : Set α where
  constructor tt

first : ∀ {α β γ} {A : Set α} {B : Set β} {C : A -> Set γ}
      -> (∀ x -> C x) -> (p : A × B) -> C (proj₁ p) × B
first f (x , y) = f x , y

second : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : A -> Set γ}
       -> (∀ {x} -> B x -> C x) -> Σ A B -> Σ A C
second g (x , y) = x , g y

third : ∀ {α β γ δ} {A : Set α} {B : A -> Set β}
          {C : ∀ {x} -> B x -> Set γ} {D : ∀ {x} -> B x -> Set δ}
      -> (∀ {x} {y : B x} -> C y -> D y) -> (∃ λ x -> Σ (B x) C) -> ∃ λ x -> Σ (B x) D
third h (x , y , z) = x , y , h z

instance
  inst-refl : ∀ {α} {A : Set α} {x : A} -> x ≡ x
  inst-refl = refl

  inst-comma : ∀ {α β} {A : Set α} {B : A -> Set β} {{x : A}} {{y : B x}} -> Σ A B
  inst-comma {{x}} {{y}} = x , y

  inst-inj₁ : ∀ {α β} {A : Set α} {B : Set β} {{x : A}} -> A ⊎ B
  inst-inj₁ {{x}} = inj₁ x

  inst-inj₂ : ∀ {α β} {A : Set α} {B : Set β} {{y : B}} -> A ⊎ B
  inst-inj₂ {{y}} = inj₂ y
