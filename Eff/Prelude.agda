module Eff.Prelude where

open import Level renaming (zero to lzero; suc to lsuc) public
open import Function public
open import Data.Nat.Base hiding (_⊔_; fold) public
open import Data.Fin using (Fin; zero; suc) public
open import Data.Sum       renaming (map to smap) public
open import Data.Product   renaming (map to pmap) public
open import Data.List.Base renaming (map to lmap) hiding (foldr; zip) public

infix 4 _≅_

data ⊥ {α} : Set α where
record ⊤ {α} : Set α where
  constructor tt

data _≅_ {α} {A : Set α} (x : A) : ∀ {β} {B : Set β} -> B -> Set where
  hrefl : x ≅ x

hsym : ∀ {α β} {A : Set α} {B : Set β} {x : A} {y : B} -> x ≅ y -> y ≅ x
hsym hrefl = hrefl

instance
  refl-instance : ∀ {α} {A : Set α} {x : A} -> x ≅ x
  refl-instance = hrefl

  inj₁-instance : ∀ {α β} {A : Set α} {B : Set β} {{x : A}} -> A ⊎ B
  inj₁-instance {{x}} = inj₁ x

  inj₂-instance : ∀ {α β} {A : Set α} {B : Set β} {{x : B}} -> A ⊎ B
  inj₂-instance {{y}} = inj₂ y

-- left, right

first : ∀ {α β γ} {A : Set α} {B : Set β} {C : A -> Set γ}
      -> (∀ x -> C x) -> (p : A × B) -> C (proj₁ p) × B
first f (x , y) = f x , y

second : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : A -> Set γ}
       -> (∀ {x} -> B x -> C x) -> Σ A B -> Σ A C
second g (x , y) = x , g y

record Tag {α β} {A : Set α} (B : A -> Set β) (x : A) : Set β where
  constructor tag
  field detag : B x
  tagOf = x
open Tag public

Tag₂ : ∀ {α β γ} {A : Set α} {B : A -> Set β} -> (∀ x -> B x -> Set γ) -> ∀ x -> B x -> Set γ
Tag₂ C x y = Tag (uncurry C) (x , y)

tagWith : ∀ {α β} {A : Set α} {B : (x : A) -> Set β} -> (x : A) -> B x -> Tag B x
tagWith _ = tag

hsubst : ∀ {α β} {A : Set α} {x y} -> (B : A -> Set β) -> x ≅ y -> B x -> B y
hsubst B hrefl = id

module _ where
  open import Relation.Binary.PropositionalEquality.TrustMe

  hSubst : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : A -> Set γ} {x} -> B ≅ C -> B x -> C x
  hSubst {β = β} {γ} rewrite trustMe {x = β} {γ} = hsubst (_$ _)
