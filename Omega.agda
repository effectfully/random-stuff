open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Nat.Properties.Simple
open import Data.Product

record Apply {α β} {A : Set α} (B : A -> Set β) x : Set β where
  constructor wrap
  field unwrap : B x
open Apply

record Universe : Set₁ where
  constructor Ψ
  field
    {Code}  : Set
    ⟦_/_⟧   : Code -> Set
open Universe

mutual
  data Typeᵤ U : Set where
    π σ  : ∀ a -> (⟦ U / a ⟧ᵤ -> Typeᵤ U) -> Typeᵤ U
    code : Typeᵤ U
    at   : Code U -> Typeᵤ U

  ⟦_/_⟧ᵤ : ∀ U -> Typeᵤ U -> Set
  ⟦ U / π a b ⟧ᵤ = ∀   x -> ⟦ U / b x ⟧ᵤ
  ⟦ U / σ a b ⟧ᵤ = ∃ λ x -> ⟦ U / b x ⟧ᵤ
  ⟦ U / code  ⟧ᵤ = Code U
  ⟦ U / at c  ⟧ᵤ = ⟦ U / c ⟧

data Type₀ : Set where
  nat₀ : Type₀

⟦_⟧₀ : Type₀ -> Set
⟦ nat₀ ⟧₀ = ℕ

{-# TERMINATING #-}
mutual
  Type : ℕ -> Set
  Type = Apply (Typeᵤ ∘ univ)

  ⟦_⟧ : ∀ {n} -> Type n -> Set
  ⟦_⟧ = ⟦ _ /_⟧ᵤ ∘ unwrap

  univ : ℕ -> Universe
  univ  0      = record { Code = Type₀  ; ⟦_/_⟧ = ⟦_⟧₀ }
  univ (suc n) = record { Code = Type n ; ⟦_/_⟧ = ⟦_⟧  }

infixr 5 _‵π‵_ _⇒_

_‵π‵_ : ∀ {n} -> (a : Type n) -> (⟦ a ⟧ -> Type n) -> Type n
a ‵π‵ b = wrap (π (unwrap a) (unwrap ∘ b))

_⇒_ : ∀ {n} -> Type n -> Type n -> Type n
a ⇒ b = a ‵π‵ const b

Type⁺ : ℕ -> Set
Type⁺ n = ∀ {m} -> Type (n + m)

lift₀ : Type 0 -> Type⁺ 0
lift₀ a {0}     = a
lift₀ a {suc m} = wrap (at (lift₀ a))

lift : ∀ {n} -> Type n -> Type⁺ n
lift {n} a {m} = subst Type (+-comm m n) (go m a) where
  go : ∀ {n} m -> Type n -> Type (m + n)
  go  0      a = a
  go (suc m) a = wrap (at (go m a))

nat : Type⁺ 0
nat = lift₀ (wrap (at nat₀))

type : ∀ n -> Type⁺ (suc n)
type n = lift {suc n} (wrap code)

mutual
  data Ω : Set where
    π σ : ∀ a -> (⟦ a ⟧ₒ -> Ω) -> Ω
    emb : ∀ {n} -> Type n -> Ω

  ⟦_⟧ₒ : Ω -> Set
  ⟦ π a b ⟧ₒ = ∀   x -> ⟦ b x ⟧ₒ
  ⟦ σ a b ⟧ₒ = ∃ λ x -> ⟦ b x ⟧ₒ
  ⟦ emb a ⟧ₒ = ⟦ a ⟧

natₒ : Ω
natₒ = emb (nat {0})

typeₒ : ℕ -> Ω
typeₒ n = emb (type n {0})

ω : Ω
ω = π natₒ typeₒ

test₁ : ⟦ Type 3 ∋ type 1 ⟧ ≡ Type 1
test₁ = refl

test₂ : ⟦ Type 3 ∋ type 2 ⟧ ≡ Type 2
test₂ = refl

test₃ : Type 4
test₃ = nat ⇒ (type 3 ⇒ type 1) ⇒ type 2

test₄ : Type 3
test₄ = type 1 ‵π‵ λ a -> lift a ⇒ type 2 ‵π‵ λ b -> nat ⇒ lift b

test₅ : ⟦ test₄ ⟧ ≡ ((a : Type 1) -> ⟦ a ⟧ -> (b : Type 2) -> ℕ -> ⟦ b ⟧)
test₅ = refl

-- fail₁ : ∀ {n} -> ⟦ type n {0} ⟧ ≡ Type n
-- fail₁ = refl

test₆ : ⟦ typeₒ 2 ⟧ₒ ≡ Type 2
test₆ = refl

test₇ : ⟦ ω ⟧ₒ ≡ ∀ n -> ⟦ type n {0} ⟧
test₇ = refl
