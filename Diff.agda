open import Function
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Base
open import Data.Fin using (Fin; zero; suc)

infixr 9 _∘ᵈ_

record Diff (k : ℕ -> ℕ) : Set where
  field βk : ∀ {n} -> k (suc n) ≡ suc (k n)

  module Kit {n α} (A : ℕ -> Set α) where
    ink  : A (suc (k n)) -> A (k (suc n))
    ink  = subst A (sym βk)

    outk : A (k (suc n)) -> A (suc (k n))
    outk = subst A βk

    unink  : ∀ {β} {B : Set β} -> (f : ∀ {n} -> (x : A n) -> B) -> f ∘ ink ≗ f
    unink  f x rewrite βk {n} = refl

    unoutk : ∀ {β} {B : Set β} -> (f : ∀ {n} -> (x : A n) -> B) -> f ∘ outk ≗ f 
    unoutk f x rewrite βk {n} = refl

    ink-outk : ink ∘ outk ≗ id
    ink-outk x rewrite βk {n} = refl

    outk-ink : outk ∘ ink ≗ id
    outk-ink x rewrite βk {n} = refl

module DiffKit {k} (d : Diff k) where
  open Diff d public
  open Kit public

module DiffKitOver {α k} (A : ℕ -> Set α) (d : Diff k) where
  open Diff d public
  private open module Dummy {n} = Kit {n} A public

dzero : Diff id
dzero = record { βk = refl }

module _ {k} (d : Diff k) where
  open Diff d

  dsucˡ : Diff (suc ∘ k)
  dsucˡ = record { βk = cong suc βk }

  dsucʳ : Diff (k ∘ suc)
  dsucʳ = record { βk = βk }

dnum : ∀ n -> Diff (n +_)
dnum  0      = dzero
dnum (suc n) = dsucˡ (dnum n)

dtop : Diff suc
dtop = dnum 1

_∘ᵈ_ : ∀ {k₂ k₁} -> Diff k₂ -> Diff k₁ -> Diff (k₂ ∘ k₁)
_∘ᵈ_ {k₂} d₂ d₁ = let open Diff in record { βk = trans (cong k₂ (βk d₁)) (βk d₂) }

module _ {k} (d : Diff k) where
  open DiffKitOver Fin d

  injectd : ∀ {n} -> Fin n -> Fin (k n)
  injectd  zero   = ink  zero
  injectd (suc i) = ink (suc (injectd i))

inject+′ : ∀ {n} m -> Fin n -> Fin (m + n)
inject+′ m = injectd (dnum m)
