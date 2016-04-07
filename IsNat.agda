-- `IsNat` is the same thing as `IsNatAt`,
-- but without any universe polymorphism related problems.

open import Level as L using (_⊔_)
open import Function
open import Data.Unit.Base
open import Data.Nat.Base hiding (_⊔_)
open import Data.List.Base

elimℕ : ∀ {π}
      -> (P : ℕ -> Set π)
      -> (∀ {n} -> P n -> P (suc n))
      -> P 0
      -> ∀ n
      -> P n
elimℕ P f z  0      = z
elimℕ P f z (suc n) = f (elimℕ P f z n)  

elimList : ∀ {α π} {A : Set α}
         -> (P : List A -> Set π)
         -> (∀ {xs} x -> P xs -> P (x ∷ xs))
         -> P []
         -> ∀ xs
         -> P xs
elimList P f z  []      = z
elimList P f z (x ∷ xs) = f x (elimList P f z xs)  

record HasNat {α} (A : Set α) : Set α where
  field
    gzero : A
    gsuc  : A -> A

  data SingNat : A -> Set α where
    szero : SingNat gzero
    ssuc  : ∀ {n} -> SingNat n -> SingNat (gsuc n)

  elimSingNat : ∀ {n π}
              -> (P : A -> Set π)
              -> (∀ {n} -> P n -> P (gsuc n))
              -> P gzero
              -> SingNat n
              -> P n
  elimSingNat P f z  szero    = z
  elimSingNat P f z (ssuc sn) = f (elimSingNat P f z sn)  
open HasNat {{...}}

record IsNat {α} (A : Set α) {{hasNat : HasNat A}} : Set α where
  field
    singNat : (n : A) -> SingNat n
open IsNat {{...}}

instance
  hasNatℕ : HasNat ℕ
  hasNatℕ = record { gzero = 0 ; gsuc = suc }

  isNatℕ : IsNat ℕ
  isNatℕ = record { singNat = elimℕ SingNat ssuc szero }

  hasNatList⊤ : HasNat (List ⊤)
  hasNatList⊤ = record { gzero = [] ; gsuc = _ ∷_ }

  isNatList⊤ : IsNat (List ⊤)
  isNatList⊤ = record { singNat = elimList SingNat (const ssuc) szero }

record IsNatAt {α} π (A : Set α) {{hasNat : HasNat A}} : Set (α ⊔ L.suc π) where
  field
    elimNat : (P : A -> Set π)
            -> (∀ {n} -> P n -> P (gsuc n))
            -> P gzero
            -> ∀ n
            -> P n

isNatIsNatAt : ∀ {α π} {A : Set α} {{hasNat : HasNat A}} {{isNat : IsNat A}} -> IsNatAt π A
isNatIsNatAt = record { elimNat = λ P f z -> elimSingNat P f z ∘ singNat }

isNatAtIsNat : ∀ {α} {A : Set α} {{hasNat : HasNat A}}
             -> (isNat : ∀ {π} -> IsNatAt π A) -> IsNat A
isNatAtIsNat isNat = record { singNat = elimNat SingNat ssuc szero }
  where open IsNatAt isNat
