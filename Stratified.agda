{-# OPTIONS --no-positivity-check #-}

open import Level renaming (zero to lzero; suc to lsuc)
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit.Base
open import Data.Nat.Base hiding (_⊔_)
open import Data.Maybe.Base
open import Data.Product

Enum : ℕ -> Set
Enum  0            = ⊥
Enum  1            = ⊤
Enum (suc (suc n)) = Maybe (Enum (suc n))

mutual
  data Type : Level -> Set where
    nat  : Type lzero
    enum : ℕ -> Type lzero
    type : ∀ α -> Type (lsuc α)
    π σ  : ∀ {α β} -> (A : Type α) -> (⟦ A ⟧ -> Type β) -> Type (α ⊔ β)
    desc : ∀ {ι} -> Type ι -> ∀ α -> Type α
    mu   : ∀ {ι α} -> (I : Type ι) -> Desc I α -> ⟦ I ⟧ -> Type α

  ⟦_⟧ : ∀ {α} -> Type α -> Set
  ⟦ nat      ⟧ = ℕ
  ⟦ enum n   ⟧ = Enum n
  ⟦ type α   ⟧ = Type α
  ⟦ π A B    ⟧ = ∀   x -> ⟦ B x ⟧
  ⟦ σ A B    ⟧ = ∃ λ x -> ⟦ B x ⟧
  ⟦ desc I α ⟧ = Desc I α
  ⟦ mu I D i ⟧ = μ D i

  data UntiedDesc {ι} (I : Type ι) ω : Level -> Set where
    var : ⟦ I ⟧ -> UntiedDesc I ω ω
    π   : ∀ {α β} -> (A : Type α) -> (⟦ A ⟧ -> UntiedDesc I ω β) -> UntiedDesc I ω (α ⊔ β)
    _⊛_ : ∀ {α β} -> UntiedDesc I ω α -> UntiedDesc I ω β -> UntiedDesc I ω (α ⊔ β)

  Desc : ∀ {ι} -> Type ι -> Level -> Set
  Desc I α = UntiedDesc I α α

  ⟦_⟧ᴰ : ∀ {ι ω α} {I : Type ι} -> UntiedDesc I ω α -> (⟦ I ⟧ -> Set) -> Set
  ⟦ var i ⟧ᴰ F = F i
  ⟦ π A D ⟧ᴰ F = ∀ x -> ⟦ D x ⟧ᴰ F
  ⟦ D ⊛ E ⟧ᴰ F = ⟦ D ⟧ᴰ F × ⟦ E ⟧ᴰ F

  Extend : ∀ {ι ω α} {I : Type ι} -> UntiedDesc I ω α -> (⟦ I ⟧ -> Set) -> ⟦ I ⟧ -> Set
  Extend (var j) F i = j ≡ i
  Extend (π A D) F i = ∃ λ x -> Extend (D x) F i
  Extend (D ⊛ E) F i = ⟦ D ⟧ᴰ F × Extend E F i

  record μ {ι α} {I : Type ι} (D : Desc I α) i : Set where
    inductive
    constructor node
    field knot : Extend D (μ D) i


pattern #₀ p = node (nothing , p)
pattern #₁ p = node (just nothing , p)

pattern !#₀ p = node (tt , p)
pattern !#₁ p = node (just tt , p)

fin : ℕ -> Type lzero
fin = mu nat $ π (enum 2) λ
          {  nothing  -> π nat λ n -> var (suc n)
          ; (just tt) -> π nat λ n -> var n ⊛ var (suc n)
          }

Fin : ℕ -> Set
Fin n = ⟦ fin n ⟧

pattern fzero {n}  = #₀ (n , refl)
pattern fsuc {n} i = !#₁ (n , i , refl)

elimFin : ∀ {n}
        -> (P : ∀ {n} -> Fin n -> Set)
        -> (∀ {n} {i : Fin n} -> P i -> P (fsuc i))
        -> (∀ {n} -> P (fzero {n}))
        -> (i : Fin n)
        -> P i
elimFin P f z  fzero   = z
elimFin P f z (fsuc i) = f (elimFin P f z i)



vec : ∀ {α} -> Type α -> ℕ -> Type α
vec A = mu nat $ π (enum 2) λ
          {  nothing  -> var 0
          ; (just tt) -> π nat λ n -> π A λ _ -> var n ⊛ var (suc n)
          }

Vec : ∀ {α} -> Type α -> ℕ -> Set
Vec A n = ⟦ vec A n ⟧

pattern []ᵥ           = #₀ refl
pattern _∷ᵥ_ {n} x xs = !#₁ (n , x , xs , refl)

elimVec : ∀ {n α} {A : Type α}
        -> (P : ∀ {n} -> Vec A n -> Set)
        -> (∀ {n} {xs : Vec A n} x -> P xs -> P (x ∷ᵥ xs))
        -> P []ᵥ
        -> (xs : Vec A n)
        -> P xs
elimVec P f z  []ᵥ      = z
elimVec P f z (x ∷ᵥ xs) = f x (elimVec P f z xs)



-- Not perfect and perhaps doesn't scale well, but works at least.
lookup : ∀ {n α} {A : Type α} -> Fin n -> Vec A n -> ⟦ A ⟧
lookup  fzero   (x ∷ᵥ xs) = x
lookup (fsuc i) (x ∷ᵥ xs) = lookup i xs
lookup  fzero   (#₀ ())
lookup (fsuc i) (#₀ ())
