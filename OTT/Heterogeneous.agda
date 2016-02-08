{-# OPTIONS --no-positivity-check #-}

open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Nat.Base
open import Data.Fin using (Fin; zero; suc)
open import Data.Product

infix 3 _≃_ _≅_[_]

dsubst : ∀ {α β} {A : Set α} {x y}
       -> (B : A -> Set β) -> Dec (x ≡ y) -> B x -> (x ≢ y -> B y) -> B y
dsubst B (yes refl) y f = y
dsubst B (no  c)    y f = f c

≟-refl : ∀ n -> (n ≟ n) ≡ yes refl
≟-refl n with n ≟ n
... | yes refl = refl
... | no  c    = ⊥-elim (c refl)

mutual
  data Type : ℕ -> Set where
    fin  : ℕ -> Type 0
    type : ∀ α -> Type (suc α)
    σ π  : ∀ {α β} -> (A : Type α) -> (⟦ A ⟧ᵀ -> Type β) -> Type (α ⊔ β)

  ⟦_⟧ᵀ : ∀ {α} -> Type α -> Set
  ⟦ fin n  ⟧ᵀ = Fin n
  ⟦ type α ⟧ᵀ = Type α
  ⟦ σ A B  ⟧ᵀ = Σ ⟦ A ⟧ᵀ λ x -> ⟦ B x ⟧ᵀ
  ⟦ π A B  ⟧ᵀ = (x : ⟦ A ⟧ᵀ) -> ⟦ B x ⟧ᵀ

data _≃_ : ∀ {α β} -> Type α -> Type β -> Set
data _≅_[_] : ∀ {α β} {A : Type α} {B : Type β} -> ⟦ A ⟧ᵀ -> ⟦ B ⟧ᵀ -> A ≃ B -> Set
coerce : ∀ {α β} {A : Type α} {B : Type β} -> A ≃ B -> ⟦ A ⟧ᵀ -> ⟦ B ⟧ᵀ
coherence : ∀ {α β} {A : Type α} {B : Type β} {x : ⟦ A ⟧ᵀ} -> (P : A ≃ B) -> x ≅ coerce P x [ P ]

data _≃_ where
  f≃f : ∀ {n} -> fin n  ≃ fin n
  t≃t : ∀ {α} -> type α ≃ type α
  σ≃σ : ∀ {α₁ α₂ β₁ β₂} {A₁ : Type α₁} {A₂ : Type α₂}
          {B₁ : ⟦ A₁ ⟧ᵀ -> Type β₁} {B₂ : ⟦ A₂ ⟧ᵀ -> Type β₂}
      -> (P : A₁ ≃ A₂) -> (∀ {x₁ x₂} -> x₁ ≅ x₂ [ P ] -> B₁ x₁ ≃ B₂ x₂) -> σ A₁ B₁ ≃ σ A₂ B₂
  π≃π : ∀ {α₁ α₂ β₁ β₂} {A₁ : Type α₁} {A₂ : Type α₂}
          {B₁ : ⟦ A₁ ⟧ᵀ -> Type β₁} {B₂ : ⟦ A₂ ⟧ᵀ -> Type β₂}
      -> (P : A₂ ≃ A₁) -> (∀ {x} -> B₁ (coerce P x) ≃ B₂ x) -> π A₁ B₁ ≃ π A₂ B₂

data _≅_[_] where
  i≃i : ∀ {n} {i : Fin n}  -> i ≅ i [ f≃f ]
  A≅A : ∀ {α} {A : Type α} -> A ≅ A [ t≃t ]
  ,≅, : ∀ {α₁ α₂ β₁ β₂} {A₁ : Type α₁} {A₂ : Type α₂}
          {B₁ : ⟦ A₁ ⟧ᵀ -> Type β₁} {B₂ : ⟦ A₂ ⟧ᵀ -> Type β₂}
          {x₁ : ⟦ A₁ ⟧ᵀ} {x₂ : ⟦ A₂ ⟧ᵀ} {y₁ : ⟦ B₁ x₁ ⟧ᵀ} {y₂ : ⟦ B₂ x₂ ⟧ᵀ}
      -> (P : A₁ ≃ A₂)
      -> (Q : ∀ {x₁ x₂} -> x₁ ≅ x₂ [ P ] -> B₁ x₁ ≃ B₂ x₂)
      -> (p : x₁ ≅ x₂ [ P ])
      -> y₁ ≅ y₂ [ Q p ]
      -> x₁ , y₁ ≅ x₂ , y₂ [ σ≃σ P Q ]
  λ≅λ : ∀ {α₁ α₂ β₁ β₂} {A₁ : Type α₁} {A₂ : Type α₂}
          {B₁ : ⟦ A₁ ⟧ᵀ -> Type β₁} {B₂ : ⟦ A₂ ⟧ᵀ -> Type β₂}
          {f₁ : ⟦ π A₁ B₁ ⟧ᵀ} {f₂ : ⟦ π A₂ B₂ ⟧ᵀ}
      -> (P : A₂ ≃ A₁)
      -> (Q : ∀ {x} -> B₁ (coerce P x) ≃ B₂ x)
      -> (∀ x -> f₁ (coerce P x) ≅ f₂ x [ Q ])
      -> f₁ ≅ f₂ [ π≃π P Q ]

fin-inj : ∀ {n m} -> fin n ≃ fin m -> n ≡ m
fin-inj f≃f = refl

type-inj : ∀ {α β} -> type α ≃ type β -> α ≡ β
type-inj t≃t = refl

σ-inj : ∀ {α₁ α₂ β₁ β₂} {A₁ : Type α₁} {A₂ : Type α₂}
          {B₁ : ⟦ A₁ ⟧ᵀ -> Type β₁} {B₂ : ⟦ A₂ ⟧ᵀ -> Type β₂}
      -> σ A₁ B₁ ≃ σ A₂ B₂ -> Σ (A₁ ≃ A₂) λ P -> ∀ {x₁ x₂} -> x₁ ≅ x₂ [ P ] -> B₁ x₁ ≃ B₂ x₂
σ-inj (σ≃σ P Q) = P , Q

π-inj : ∀ {α₁ α₂ β₁ β₂} {A₁ : Type α₁} {A₂ : Type α₂}
          {B₁ : ⟦ A₁ ⟧ᵀ -> Type β₁} {B₂ : ⟦ A₂ ⟧ᵀ -> Type β₂}
      -> π A₁ B₁ ≃ π A₂ B₂ -> Σ (A₂ ≃ A₁) λ P -> ∀ {x} -> B₁ (coerce P x) ≃ B₂ x
π-inj (π≃π P Q) = P , Q

coerce {A = fin n  } {fin m  } P i = dsubst Fin  (n ≟ m) i (λ c -> ⊥-elim (c (fin-inj  P)))
coerce {A = type α } {type β } P A = dsubst Type (α ≟ β) A (λ c -> ⊥-elim (c (type-inj P)))
coerce {A = σ A₁ B₁} {σ A₂ B₂} P p = coerce (proj₁ (σ-inj P)) (proj₁ p)
                                   , coerce (proj₂ (σ-inj P) (coherence (proj₁ (σ-inj P)))) (proj₂ p)
coerce {A = π A₁ B₁} {π A₂ B₂} P f = λ x -> coerce (proj₂ (π-inj P)) (f (coerce (proj₁ (π-inj P)) x))

coerce {A = fin _ } {type _} ()
coerce {A = fin _ } {σ _ _ } ()
coerce {A = fin _ } {π _ _ } ()
coerce {A = type _} {fin x } ()
coerce {A = type _} {σ _ _ } ()
coerce {A = type _} {π _ _ } ()
coerce {A = σ _ _ } {fin _ } ()
coerce {A = σ _ _ } {type _} ()
coerce {A = σ _ _ } {π _ _ } ()
coerce {A = π _ _ } {fin _ } ()
coerce {A = π _ _ } {type _} ()
coerce {A = π _ _ } {σ _ _ } ()

coherence (f≃f {n}) rewrite ≟-refl n = i≃i
coherence (t≃t {α}) rewrite ≟-refl α = A≅A
coherence (σ≃σ P Q) = ,≅, P Q (coherence P) (coherence (Q (coherence P)))
coherence (π≃π P Q) = λ≅λ P Q λ x -> coherence Q
