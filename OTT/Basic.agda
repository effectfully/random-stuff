{-# OPTIONS --no-positivity-check --no-termination-check #-}

open import Function
open import Data.Empty
open import Data.Unit.Base
open import Data.Nat.Base
open import Data.Fin using (Fin; zero; suc)
open import Data.Product

infixl 6 _⊔₀_
infix  3 _≃_ _≅_
infix  5 _≟ₙ_
infix  1 _&_
infix  2 _⇒_

_⊔₀_ : ℕ -> ℕ -> ℕ
α ⊔₀ 0 = 0
α ⊔₀ β = α ⊔ β

mutual
  Prop = Univ 0
  Type = Univ ∘ suc

  data Univ : ℕ -> Set where
    bot  : Prop
    top  : Prop
    univ : ∀ α -> Univ (suc α)
    σ    : ∀ {α β} -> (A : Univ α) -> (⟦ A ⟧ᵀ -> Univ β) -> Univ (α ⊔  β)
    π    : ∀ {α β} -> (A : Univ α) -> (⟦ A ⟧ᵀ -> Univ β) -> Univ (α ⊔₀ β)

  ⟦_⟧ᵀ : ∀ {α} -> Univ α -> Set
  ⟦ bot    ⟧ᵀ = ⊥
  ⟦ top    ⟧ᵀ = ⊤
  ⟦ univ α ⟧ᵀ = Univ α
  ⟦ σ A B  ⟧ᵀ = Σ ⟦ A ⟧ᵀ λ x -> ⟦ B x ⟧ᵀ
  ⟦ π A B  ⟧ᵀ = (x : ⟦ A ⟧ᵀ) -> ⟦ B x ⟧ᵀ 

prop = univ 0
type = univ ∘ suc

_&_ : ∀ {α β} -> Univ α -> Univ β -> Univ (α ⊔  β)
A & B = σ A λ _ -> B

_⇒_ : ∀ {α β} -> Univ α -> Univ β -> Univ (α ⊔₀ β)
A ⇒ B = π A λ _ -> B

_≟ₙ_ : ℕ -> ℕ -> Prop
zero  ≟ₙ zero  = top
suc n ≟ₙ suc m = n ≟ₙ m
_     ≟ₙ _     = bot

mutual
  _≃_ : ∀ {α β} -> Univ α -> Univ β -> Prop
  bot     ≃ bot     = top
  top     ≃ top     = top
  univ α  ≃ univ β  = α ≟ₙ β
  σ A₁ B₁ ≃ σ A₂ B₂ = A₁ ≃ A₂ & π _ λ x₁ -> π _ λ x₂ -> x₁ ≅ x₂ ⇒ B₁ x₁ ≃ B₂ x₂
  π A₁ B₁ ≃ π A₂ B₂ = A₂ ≃ A₁ & π _ λ x₁ -> π _ λ x₂ -> x₂ ≅ x₁ ⇒ B₁ x₁ ≃ B₂ x₂
  _       ≃ _       = bot

  _≅_ : ∀ {α β} {A : Univ α} {B : Univ β} -> ⟦ A ⟧ᵀ -> ⟦ B ⟧ᵀ -> Prop
  _≅_ {A = bot    } {bot    } _  _  = top
  _≅_ {A = top    } {top    } _  _  = top
  _≅_ {A = univ α } {univ β } u₁ u₂ = u₁ ≃ u₂
  _≅_ {A = σ A₁ B₁} {σ A₂ B₂} p₁ p₂ = let (x₁ , y₁) , (x₂ , y₂) = p₁ , p₂ in
    σ (x₁ ≅ x₂) λ _ -> y₁ ≅ y₂
  _≅_ {A = π A₁ B₁} {π A₂ B₂} f₁ f₂ = π _ λ x₁ -> π _ λ x₂ -> x₁ ≅ x₂ ⇒ f₁ x₁ ≅ f₂ x₂
  x ≅ y = bot

coerceUnivᵏ : ∀ {α β} -> (k : ℕ -> ℕ) -> ⟦ α ≟ₙ β ⟧ᵀ -> Univ (k α) -> Univ (k β)
coerceUnivᵏ {0}     {0}     k P  A = A
coerceUnivᵏ {suc α} {suc β} k P  A = coerceUnivᵏ (k ∘ suc) P A
coerceUnivᵏ {0}     {suc _} k () A
coerceUnivᵏ {suc _} {0}     k () A

coerceUniv : ∀ {α β} -> ⟦ α ≟ₙ β ⟧ᵀ -> Univ α -> Univ β
coerceUniv = coerceUnivᵏ id

mutual
  coerce : ∀ {α β} {A : Univ α} {B : Univ β} -> ⟦ A ≃ B ⟧ᵀ -> ⟦ A ⟧ᵀ -> ⟦ B ⟧ᵀ
  coerce {A = bot    } {bot    } P ()
  coerce {A = top    } {top    } P _  = _
  coerce {A = univ α } {univ β } P A  = coerceUniv P A
  coerce {A = σ A₁ B₁} {σ A₂ B₂} P p  = let P₁ , P₂ = P ; x , y = p in
    coerce P₁ x , coerce (P₂ x (coerce P₁ x) (coherence P₁ x)) y
  coerce {A = π A₁ B₁} {π A₂ B₂} P f  = let P₁ , P₂ = P in λ x ->
    coerce (P₂ (coerce P₁ x) x (coherence P₁ x)) (f (coerce P₁ x))
  coerce {A = bot   } {top   } ()
  coerce {A = bot   } {univ _} ()
  coerce {A = bot   } {σ _ _ } ()
  coerce {A = bot   } {π _ _ } ()
  coerce {A = top   } {bot   } ()
  coerce {A = top   } {univ _} ()
  coerce {A = top   } {σ _ _ } ()
  coerce {A = top   } {π _ _ } ()
  coerce {A = univ _} {bot   } ()
  coerce {A = univ _} {top   } ()
  coerce {A = univ _} {σ _ _ } ()
  coerce {A = univ _} {π _ _ } ()
  coerce {A = σ _ _ } {bot   } ()
  coerce {A = σ _ _ } {top   } ()
  coerce {A = σ _ _ } {univ _} ()
  coerce {A = σ _ _ } {π _ _ } ()
  coerce {A = π _ _ } {bot   } ()
  coerce {A = π _ _ } {top   } ()
  coerce {A = π _ _ } {univ _} ()
  coerce {A = π _ _ } {σ _ _ } ()

  postulate
    coherence : ∀ {α β} {A : Univ α} {B : Univ β}
              -> (P : ⟦ A ≃ B ⟧ᵀ) -> (x : ⟦ A ⟧ᵀ) -> ⟦ x ≅ coerce P x ⟧ᵀ
