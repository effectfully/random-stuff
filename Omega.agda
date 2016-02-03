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

nat : Type⁺ 0
nat {0}     = wrap (at nat₀)
nat {suc m} = wrap (at nat)

type : ∀ n -> Type⁺ (suc n)
type n {m} = subst Type (cong suc (+-comm m n)) (go m) where
  go : ∀ {n} m -> Type (suc m + n)
  go  0      = wrap  code
  go (suc m) = wrap (at (go m))

lift : ∀ {n} -> Type n -> Type⁺ n
lift a {m} = subst Type (+-comm m _) (go m a) where
  go : ∀ {n} m -> Type n -> Type (m + n)
  go  0      a = a
  go (suc m) a = wrap (at (go m a))

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
test₄ = type 1 ‵π‵ λ a -> lift a ⇒ type 2 ‵π‵ λ b -> lift b

-- fail₁ : ∀ {n} -> ⟦ type n {0} ⟧ ≡ Type n
-- fail₁ = refl

test₅ : ⟦ typeₒ 2 ⟧ₒ ≡ Type 2
test₅ = refl

test₆ : ⟦ ω ⟧ₒ ≡ ∀ n -> ⟦ type n {0} ⟧
test₆ = refl
