open import Function
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Base

record Diff {α} (A : ℕ -> Set α) (k : ℕ -> ℕ) : Set α where
  no-eta-equality
  field
    ink  : ∀ {n} -> A (suc (k n)) -> A (k (suc n))
    outk : ∀ {n} -> A (k (suc n)) -> A (suc (k n))
    
    ink-outk : ∀ {n} {x : A (k (suc n))} -> ink (outk x) ≡ x
    outk-ink : ∀ {n} {x : A (suc (k n))} -> outk (ink x) ≡ x

DiffAt : ∀ α -> (ℕ -> ℕ) -> Set (lsuc α)
DiffAt α k = ∀ {A} -> Diff A k

module DiffAt {k} (d : ∀ {α} -> DiffAt α k) {α} A = Diff (d {α} {A})

dzero : ∀ {α} -> DiffAt α id
dzero = record
  { ink      = id
  ; outk     = id
  ; ink-outk = refl
  ; outk-ink = refl
  }

dsuc : ∀ {α k} {A : ℕ -> Set α} -> Diff A k -> Diff A (k ∘ suc)
dsuc d = record
  { ink      = ink
  ; outk     = outk
  ; ink-outk = ink-outk
  ; outk-ink = outk-ink
  } where open Diff d

dcoe : ∀ {α k} {A : ℕ -> Set α} -> Diff (A ∘ suc) k -> Diff A (suc ∘ k)
dcoe d = record
  { ink      = ink
  ; outk     = outk
  ; ink-outk = ink-outk
  ; outk-ink = outk-ink
  } where open Diff d

duncoe : ∀ {α k} {A : ℕ -> Set α} -> Diff A (suc ∘ k) -> Diff (A ∘ suc) k
duncoe d = record
  { ink      = ink
  ; outk     = outk
  ; ink-outk = ink-outk
  ; outk-ink = outk-ink
  } where open Diff d

dnum : ∀ {α} n -> DiffAt α (n +_)
dnum  0      = dzero
dnum (suc n) = dcoe (dnum n)

dtop : ∀ {α} -> DiffAt α suc
dtop = dnum 1

private
  module Example where
    open import Data.Fin using (Fin; zero; suc)

    module _ {k} (d : Diff Fin k) where
      open Diff d

      injectd : ∀ {n} -> Fin n -> Fin (k n)
      injectd  zero   = ink  zero
      injectd (suc i) = ink (suc (injectd i))

    inject+′ : ∀ {n} m -> Fin n -> Fin (m + n)
    inject+′ m = injectd (dnum m)
