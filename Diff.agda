open import Function
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Base
open import Data.Fin using (Fin; zero; suc)

infixr 9 _∘ᵈ_

record Diff {α} (A : ℕ -> Set α) (k : ℕ -> ℕ) : Set α where
  no-eta-equality
  field
    ink  : ∀ {n} -> A (suc (k n)) -> A (k (suc n))
    outk : ∀ {n} -> A (k (suc n)) -> A (suc (k n))
    
    ink-outk : ∀ {n} {x : A (k (suc n))} -> ink (outk x) ≡ x
    outk-ink : ∀ {n} {x : A (suc (k n))} -> outk (ink x) ≡ x

    -- We probably need something like
    
    -- unink  : ∀ {β} {B : ∀ {n} -> A n -> Set β}
    --        -> (f : ∀ {n} -> (x : A n) -> B x) -> f (ink x) ≡ f x
    -- unoutk : ∀ {β} {B : ∀ {n} -> A n -> Set β}
    --        -> (f : ∀ {n} -> (x : A n) -> B x) -> f (out x) ≡ f x

    -- but in a suitable (i.e. universe polymorphic, but without quantification over levels) form.
    -- Then the above equalities are derivable.

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

dright : ∀ {α k} {A : ℕ -> Set α} -> Diff (A ∘ suc) k -> Diff A (suc ∘ k)
dright d = record
  { ink      = ink
  ; outk     = outk
  ; ink-outk = ink-outk
  ; outk-ink = outk-ink
  } where open Diff d

dleft : ∀ {α k} {A : ℕ -> Set α} -> Diff A (suc ∘ k) -> Diff (A ∘ suc) k
dleft d = record
  { ink      = ink
  ; outk     = outk
  ; ink-outk = ink-outk
  ; outk-ink = outk-ink
  } where open Diff d

_∘ᵈ_ : ∀ {α k₁ k₂} {A : ℕ -> Set α} -> Diff A k₂ -> Diff (A ∘ k₂) k₁ -> Diff A (k₂ ∘ k₁)
d₂ ∘ᵈ d₁ = record
  { ink      = ink  d₁ ∘ ink  d₂
  ; outk     = outk d₂ ∘ outk d₁
  ; ink-outk = trans (cong (ink  d₁) (ink-outk d₂)) (ink-outk d₁)
  ; outk-ink = trans (cong (outk d₂) (outk-ink d₁)) (outk-ink d₂)
  } where open Diff

dnum : ∀ {α} n -> DiffAt α (n +_)
dnum  0      = dzero
dnum (suc n) = dright (dnum n)

dtop : ∀ {α} -> DiffAt α suc
dtop = dnum 1

module _ {k} (d : Diff Fin k) where
  open Diff d

  injectd : ∀ {n} -> Fin n -> Fin (k n)
  injectd  zero   = ink  zero
  injectd (suc i) = ink (suc (injectd i))

inject+′ : ∀ {n} m -> Fin n -> Fin (m + n)
inject+′ m = injectd (dnum m)

