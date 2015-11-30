{-# OPTIONS --no-positivity-check --no-termination-check #-}

open import Function hiding (_⟨_⟩_)
open import Data.Empty
open import Data.Unit.Base
open import Data.Nat.Base
open import Data.Fin using (Fin; zero; suc)
open import Data.Product

infixl 6 _⊔₀_
infixl 4 _≈_
infixl 3 _≃_
infix  3 _≊_
infix  5 _≟ₙ_
infix  1 _&_
infix  2 _⇒_

module _ where
  open import Level renaming (_⊔_ to _⊔ₗ_)
  open import Relation.Binary.PropositionalEquality hiding ([_])
  open import Relation.Binary.HeterogeneousEquality hiding ([_])

  infix  2 _/_
  infixl 1 _⌈_⌉_

  record [_]_≅_ {ι α} {I : Set ι} {i j} (A : I -> Set α) (x : A i) (y : A j) : Set (ι ⊔ₗ α) where
    constructor _/_
    field
      ind : i ≡ j
      val : x ≅ y

  irefl : ∀ {ι α} {I : Set ι} {A : I -> Set α} {i} {x : A i} -> [ A ] x ≅ x
  irefl = refl / refl

  coerceBy : ∀ {ι α β} {I : Set ι} {A : I -> Set α}
               {B : ∀ {k} -> A k -> Set β} {i j} {x : A i} {y : A j}
           -> [ A ] x ≅ y -> B x -> B y
  coerceBy (refl / refl) = id

  _⌈_⌉_ : ∀ {ι α} {I : Set ι} {A : I -> Set α} {i₁ i₂ j₁ j₂}
            {x₁ : A i₁} {x₂ : A i₂} {y₁ : A j₁} {y₂ : A j₂}
        -> [ A ] x₁ ≅ x₂ -> [ A ] x₁ ≅ y₁ -> [ A ] y₁ ≅ y₂ -> [ A ] x₂ ≅ y₂
  refl / refl ⌈ refl / refl ⌉ refl / refl = refl / refl

_⊔₀_ : ℕ -> ℕ -> ℕ
α ⊔₀ 0 = 0
α ⊔₀ β = α ⊔ β

mutual
  Prop = Univ 0
  Type = Univ ∘ suc

  data Univ : ℕ -> Set where
    bot  : Prop
    top  : Prop
    _≈_  : ∀ {α β} -> Univ α -> Univ β -> Prop
    univ : ∀ α -> Type α
    σ    : ∀ {α β} -> (A : Univ α) -> (⟦ A ⟧ -> Univ β) -> Univ (α ⊔  β)
    π    : ∀ {α β} -> (A : Univ α) -> (⟦ A ⟧ -> Univ β) -> Univ (α ⊔₀ β)

  ⟦_⟧ : ∀ {α} -> Univ α -> Set
  ⟦ bot    ⟧ = ⊥
  ⟦ top    ⟧ = ⊤
  ⟦ A ≈ B  ⟧ = [ Univ ] A ≅ B
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

mutual
  _≃_ : ∀ {α β} -> Univ α -> Univ β -> Prop
  bot     ≃ bot     = top
  top     ≃ top     = top
  A₁ ≈ B₁ ≃ A₂ ≈ B₂ = A₁ ≈ A₂ & B₁ ≈ B₂
  univ α  ≃ univ β  = α ≟ₙ β
  σ A₁ B₁ ≃ σ A₂ B₂ = (A₁ ≃ A₂) & π _ λ x₁ -> π _ λ x₂ -> x₁ ≊ x₂ ⇒ B₁ x₁ ≃ B₂ x₂
  π A₁ B₁ ≃ π A₂ B₂ = σ (A₂ ≈ A₁) λ P -> π _ λ x -> B₁ (coerceBy P x) ≃ B₂ x
  _       ≃ _       = bot

  _≊_ : ∀ {α β} {A : Univ α} {B : Univ β} -> ⟦ A ⟧ -> ⟦ B ⟧ -> Prop
  _≊_ {A = bot    } {bot    } _  _  = top
  _≊_ {A = top    } {top    } _  _  = top
  _≊_ {A = A₁ ≈ B₁} {A₂ ≈ B₂} _  _  = top
  _≊_ {A = univ α } {univ β } A₁ A₂ = A₁ ≃ A₂
  _≊_ {A = σ A₁ B₁} {σ A₂ B₂} p₁ p₂ = let (x₁ , y₁) , (x₂ , y₂) = p₁ , p₂ in x₁ ≊ x₂ & y₁ ≊ y₂
  _≊_ {A = π A₁ B₁} {π A₂ B₂} f₁ f₂ = σ (A₂ ≈ A₁) λ P -> π _ λ x -> f₁ (coerceBy P x) ≊ f₂ x
  _≊_                         _  _  = bot

coerceUniv+ : ∀ {α β} -> (k : ℕ -> ℕ) -> ⟦ α ≟ₙ β ⟧ -> Univ (k α) -> Univ (k β)
coerceUniv+ {0}     {0}     k r A = A
coerceUniv+ {suc α} {suc β} k r A = coerceUniv+ (k ∘ suc) r A
coerceUniv+ {0}     {suc _} k ()
coerceUniv+ {suc _} {0}     k ()

coerceUniv : ∀ {α β} -> ⟦ α ≟ₙ β ⟧ -> Univ α -> Univ β
coerceUniv = coerceUniv+ id

-- Just for fun. We don't really need more than `≃-refl'.
postulate univalence : ∀ {α β} -> (A : Univ α) -> (B : Univ β) -> ⟦ (A ≈ B) ≃ (A ≃ B) ⟧

mutual
  coerce : ∀ {α β} {A : Univ α} {B : Univ β} -> ⟦ A ≃ B ⟧ -> ⟦ A ⟧ -> ⟦ B ⟧
  coerce {A = bot    } {bot    } P ()
  coerce {A = top    } {top    } P _ = _
  coerce {A = A₁ ≈ B₁} {A₂ ≈ B₂} P p = let q₁ , q₂ = P in q₁ ⌈ p ⌉ q₂
  coerce {A = univ α } {univ β } P A = coerceUniv P A
  coerce {A = σ A₁ B₁} {σ A₂ B₂} P p = let P₁ , P₂ = P; x , y = p in
    coerce P₁ x , coerce (P₂ x (coerce P₁ x) (coherence P₁ x)) y
  coerce {A = π A₁ B₁} {π A₂ B₂} P f = let P₁ , P₂ = P in λ x -> coerce (P₂ x) (f (coerceBy P₁ x))
  coerce {A = bot   } {top   } ()
  coerce {A = bot   } {_ ≈ _ } ()
  coerce {A = bot   } {univ _} ()
  coerce {A = bot   } {σ _ _ } ()
  coerce {A = bot   } {π _ _ } ()
  coerce {A = top   } {bot   } ()
  coerce {A = top   } {_ ≈ _ } ()
  coerce {A = top   } {univ _} ()
  coerce {A = top   } {σ _ _ } ()
  coerce {A = top   } {π _ _ } ()
  coerce {A = _ ≈ _ } {bot   } ()
  coerce {A = _ ≈ _ } {top   } ()
  coerce {A = _ ≈ _ } {univ _} ()
  coerce {A = _ ≈ _ } {σ _ _ } ()
  coerce {A = _ ≈ _ } {π _ _ } ()
  coerce {A = univ _} {bot   } ()
  coerce {A = univ _} {top   } ()
  coerce {A = univ _} {_ ≈ _ } ()
  coerce {A = univ _} {σ _ _ } ()
  coerce {A = univ _} {π _ _ } ()
  coerce {A = σ _ _ } {bot   } ()
  coerce {A = σ _ _ } {top   } ()
  coerce {A = σ _ _ } {_ ≈ _ } ()
  coerce {A = σ _ _ } {univ _} ()
  coerce {A = σ _ _ } {π _ _ } ()
  coerce {A = π _ _ } {bot   } ()
  coerce {A = π _ _ } {top   } ()
  coerce {A = π _ _ } {_ ≈ _ } ()
  coerce {A = π _ _ } {univ _} ()
  coerce {A = π _ _ } {σ _ _ } ()

  coherenceUniv+ : ∀ {α β}
                 -> (k : ℕ -> ℕ) -> (r : ⟦ α ≟ₙ β ⟧) -> (A : Univ (k α)) -> ⟦ A ≃ coerceUniv+ k r A ⟧
  coherenceUniv+ {0}     {0}     k r A = coerce (univalence A A) irefl
  coherenceUniv+ {suc α} {suc β} k r A = coherenceUniv+ (k ∘ suc) r A
  coherenceUniv+ {0}     {suc _} k ()
  coherenceUniv+ {suc _} {0}     k ()

  coherenceUniv : ∀ {α β} -> (p : ⟦ α ≟ₙ β ⟧) -> (A : Univ α) -> ⟦ A ≃ coerceUniv p A ⟧
  coherenceUniv = coherenceUniv+ id

  coherence : ∀ {α β} {A : Univ α} {B : Univ β}
            -> (P : ⟦ A ≃ B ⟧) -> (x : ⟦ A ⟧) -> ⟦ x ≊ coerce P x ⟧
  coherence {A = bot    } {bot    } P ()
  coherence {A = top    } {top    } P _ = _
  coherence {A = A₁ ≈ B₁} {A₂ ≈ B₂} P p = _
  coherence {A = univ α } {univ β } P A = coherenceUniv P A
  coherence {A = σ A₁ B₁} {σ A₂ B₂} P p = let P₁ , P₂ = P ; x , y = p in
    coherence P₁ x , coherence (P₂ x (coerce P₁ x) (coherence P₁ x)) y
  coherence {A = π A₁ B₁} {π A₂ B₂} P f = let P₁ , P₂ = P in
    P₁ , λ x -> coherence (P₂ x) (f (coerceBy P₁ x))
  coherence {A = bot   } {top   } ()
  coherence {A = bot   } {_ ≈ _ } ()
  coherence {A = bot   } {univ _} ()
  coherence {A = bot   } {σ _ _ } ()
  coherence {A = bot   } {π _ _ } ()
  coherence {A = top   } {bot   } ()
  coherence {A = top   } {_ ≈ _ } ()
  coherence {A = top   } {univ _} ()
  coherence {A = top   } {σ _ _ } ()
  coherence {A = top   } {π _ _ } ()
  coherence {A = _ ≈ _ } {bot   } ()
  coherence {A = _ ≈ _ } {top   } ()
  coherence {A = _ ≈ _ } {univ _} ()
  coherence {A = _ ≈ _ } {σ _ _ } ()
  coherence {A = _ ≈ _ } {π _ _ } ()
  coherence {A = univ _} {bot   } ()
  coherence {A = univ _} {top   } ()
  coherence {A = univ _} {_ ≈ _ } ()
  coherence {A = univ _} {σ _ _ } ()
  coherence {A = univ _} {π _ _ } ()
  coherence {A = σ _ _ } {bot   } ()
  coherence {A = σ _ _ } {top   } ()
  coherence {A = σ _ _ } {_ ≈ _ } ()
  coherence {A = σ _ _ } {univ _} ()
  coherence {A = σ _ _ } {π _ _ } ()
  coherence {A = π _ _ } {bot   } ()
  coherence {A = π _ _ } {top   } ()
  coherence {A = π _ _ } {_ ≈ _ } ()
  coherence {A = π _ _ } {univ _} ()
  coherence {A = π _ _ } {σ _ _ } ()

esubst : ∀ {α π} {A : Univ α} {x y} -> (P : ⟦ A ⟧ -> Univ π) -> ⟦ x ≊ y ⟧ -> ⟦ P x ⟧ -> ⟦ P y ⟧
esubst P _ = coerce whoCares where postulate whoCares : _
