module System-F.Prelude where

open import Level renaming (zero to zeroₗ; suc to sucₗ) public
open import Function public
open import Relation.Binary.PropositionalEquality hiding ([_]) public
open import Data.Empty public
open import Data.Unit.Base hiding (_≤_) public
open import Data.Nat.Base hiding (_⊔_) public
open import Data.Fin using (Fin; zero; suc) public
open import Data.Product public
open import Data.Vec using (lookup) public

cong₃ : ∀ {α β γ δ} {A : Set α} {B : Set β} {C : Set γ} {D : Set δ} {x y v w s t}
      -> (f : A -> B -> C -> D) -> x ≡ y -> v ≡ w -> s ≡ t -> f x v s ≡ f y w t
cong₃ f refl refl refl = refl
