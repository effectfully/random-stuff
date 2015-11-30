{-# OPTIONS --no-positivity-check --no-termination-check #-}

open import Function
open import Data.Empty
open import Data.Unit.Base hiding (_≤_)
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
    univ : ∀ α -> Type α
    σ    : ∀ {α β} -> (A : Univ α) -> (⟦ A ⟧ -> Univ β) -> Univ (α ⊔  β)
    π    : ∀ {α β} -> (A : Univ α) -> (⟦ A ⟧ -> Univ β) -> Univ (α ⊔₀ β)

  ⟦_⟧ : ∀ {α} -> Univ α -> Set
  ⟦ bot    ⟧ = ⊥
  ⟦ top    ⟧ = ⊤
  ⟦ univ α ⟧ = Univ α
  ⟦ σ A B  ⟧ = Σ ⟦ A ⟧ λ x -> ⟦ B x ⟧
  ⟦ π A B  ⟧ = (x : ⟦ A ⟧) -> ⟦ B x ⟧
  
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

_≃_ : ∀ {α β} -> Univ α -> Univ β -> Prop
_≅_ : ∀ {α β} {A : Univ α} {B : Univ β} -> ⟦ A ⟧ -> ⟦ B ⟧ -> Prop
coerce : ∀ {α β} {A : Univ α} {B : Univ β} -> ⟦ A ≃ B ⟧ -> ⟦ A ⟧ -> ⟦ B ⟧
coherence : ∀ {α β} {A : Univ α} {B : Univ β}
          -> (P : ⟦ A ≃ B ⟧) -> (x : ⟦ A ⟧) -> ⟦ x ≅ coerce P x ⟧

bot     ≃ bot     = top
top     ≃ top     = top
univ α  ≃ univ β  = α ≟ₙ β
σ A₁ B₁ ≃ σ A₂ B₂ = A₁ ≃ A₂ & π _ λ x₁ -> π _ λ x₂ -> x₁ ≅ x₂ ⇒ B₁ x₁ ≃ B₂ x₂
π A₁ B₁ ≃ π A₂ B₂ = σ (A₂ ≃ A₁) λ P -> π _ λ x -> B₁ (coerce P x) ≃ B₂ x
_       ≃ _       = bot

_≅_ {A = bot    } {bot    } _  _  = top
_≅_ {A = top    } {top    } _  _  = top
_≅_ {A = univ α } {univ β } u₁ u₂ = u₁ ≃ u₂
_≅_ {A = σ A₁ B₁} {σ A₂ B₂} p₁ p₂ = let (x₁ , y₁) , (x₂ , y₂) = p₁ , p₂ in x₁ ≅ x₂ & y₁ ≅ y₂
_≅_ {A = π A₁ B₁} {π A₂ B₂} f₁ f₂ = σ (A₂ ≃ A₁) λ P -> π _ λ x -> f₁ (coerce P x) ≅ f₂ x
_≅_                         _  _  = bot 

coerceUniv+ : ∀ {α β} -> (k : ℕ -> ℕ) -> ⟦ α ≟ₙ β ⟧ -> Univ (k α) -> Univ (k β)
coerceUniv+ {0}     {0}     k r A = A
coerceUniv+ {suc α} {suc β} k r A = coerceUniv+ (k ∘ suc) r A
coerceUniv+ {0}     {suc _} k ()
coerceUniv+ {suc _} {0}     k ()

coerceUniv : ∀ {α β} -> ⟦ α ≟ₙ β ⟧ -> Univ α -> Univ β
coerceUniv = coerceUniv+ id

coerce {A = bot    } {bot    } P ()
coerce {A = top    } {top    } P _ = _
coerce {A = univ α } {univ β } P A = coerceUniv P A
coerce {A = σ A₁ B₁} {σ A₂ B₂} P p = let P₁ , P₂ = P; x , y  = p in
  coerce P₁ x , coerce (P₂ x (coerce P₁ x) (coherence P₁ x)) y
coerce {A = π A₁ B₁} {π A₂ B₂} P f = let P₁ , P₂ = P in λ x -> coerce (P₂ x) (f (coerce P₁ x))
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

postulate ≃-refl : ∀ {α} -> (A : Univ α) -> ⟦ A ≃ A ⟧

coherenceUniv+ : ∀ {α β}
               -> (k : ℕ -> ℕ) -> (r : ⟦ α ≟ₙ β ⟧) -> (A : Univ (k α)) -> ⟦ A ≃ coerceUniv+ k r A ⟧
coherenceUniv+ {0}     {0}     k r A = ≃-refl A
coherenceUniv+ {suc α} {suc β} k r A = coherenceUniv+ (k ∘ suc) r A
coherenceUniv+ {0}     {suc _} k ()
coherenceUniv+ {suc _} {0}     k ()

coherenceUniv : ∀ {α β} -> (p : ⟦ α ≟ₙ β ⟧) -> (A : Univ α) -> ⟦ A ≃ coerceUniv p A ⟧
coherenceUniv = coherenceUniv+ id

coherence {A = bot    } {bot    } P ()
coherence {A = top    } {top    } P _ = _
coherence {A = univ α } {univ β } P A = coherenceUniv P A
coherence {A = σ A₁ B₁} {σ A₂ B₂} P p = let P₁ , P₂ = P ; x , y = p in
  coherence P₁ x , coherence (P₂ x (coerce P₁ x) (coherence P₁ x)) y
coherence {A = π A₁ B₁} {π A₂ B₂} P f = let P₁ , P₂ = P in
  P₁ , λ x -> coherence (P₂ x) (f (coerce P₁ x))
coherence {A = bot   } {top   } ()
coherence {A = bot   } {univ _} ()
coherence {A = bot   } {σ _ _ } ()
coherence {A = bot   } {π _ _ } ()
coherence {A = top   } {bot   } ()
coherence {A = top   } {univ _} ()
coherence {A = top   } {σ _ _ } ()
coherence {A = top   } {π _ _ } ()
coherence {A = univ _} {bot   } ()
coherence {A = univ _} {top   } ()
coherence {A = univ _} {σ _ _ } ()
coherence {A = univ _} {π _ _ } ()
coherence {A = σ _ _ } {bot   } ()
coherence {A = σ _ _ } {top   } ()
coherence {A = σ _ _ } {univ _} ()
coherence {A = σ _ _ } {π _ _ } ()
coherence {A = π _ _ } {bot   } ()
coherence {A = π _ _ } {top   } ()
coherence {A = π _ _ } {univ _} ()
coherence {A = π _ _ } {σ _ _ } ()

esubst : ∀ {α π} {A : Univ α} {x y} -> (P : ⟦ A ⟧ -> Univ π) -> ⟦ x ≅ y ⟧ -> ⟦ P x ⟧ -> ⟦ P y ⟧
esubst P _ = coerce whoCares where postulate whoCares : _
