open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Nat.Base as Nat hiding (fold)

infixl 5 _▻_
infixr 6 _⇒_
infix  4 _∈_ _⊢_
infix  4 vs_
infixr 3 ƛ_
infixl 6 _·_

data Type : Set where
  _⇒_ : Type -> Type -> Type
  □   : Type -> Type
  nat : Type

data Con : Set where
  ε   : Con
  _▻_ : Con -> Type -> Con

data _∈_ σ : Con -> Set where
  vz  : ∀ {Γ}            -> σ ∈ Γ ▻ σ
  vs_ : ∀ {Γ τ} -> σ ∈ Γ -> σ ∈ Γ ▻ τ

mutual
  data _⊢_ Γ : Type -> Set where
    var  : ∀ {σ}   -> σ ∈ Γ         -> Γ ⊢ σ
    ƛ_   : ∀ {σ τ} -> Γ ▻ σ ⊢ τ     -> Γ ⊢ σ ⇒ τ
    _·_  : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ     -> Γ ⊢ σ       -> Γ ⊢ τ
    up   : ∀ {σ}   -> Term σ        -> Γ ⊢ □ σ
    down : ∀ {σ}   -> Γ ⊢ □ σ       -> Γ ⊢ σ
    _∙_  : ∀ {σ τ} -> Γ ⊢ □ (σ ⇒ τ) -> Γ ⊢ □ σ     -> Γ ⊢ □ τ
    elim : ∀ {σ τ} -> Γ ⊢ τ ⇒ τ ⇒ τ -> Γ ⊢ nat ⇒ τ -> Γ ⊢ τ   -> Γ ⊢ □ σ -> Γ ⊢ τ
    z    :            Γ ⊢ nat
    s    :            Γ ⊢ nat       -> Γ ⊢ nat
    fold : ∀ {τ}   -> Γ ⊢ τ ⇒ τ     -> Γ ⊢ τ       -> Γ ⊢ nat -> Γ ⊢ τ

  Term : Type -> Set
  Term σ = ε ⊢ σ

∈→ℕ : ∀ {Γ σ} -> σ ∈ Γ -> ℕ
∈→ℕ  vz    = 0
∈→ℕ (vs v) = suc (∈→ℕ v)

module _ {A : Set} (g : A -> A -> A) (f : ℕ -> A) (x : A) where
  infixr 5 _⊕_
  _⊕_ = g

  foldTerm : ∀ {Γ σ} -> Γ ⊢ σ -> A
  foldTerm (var v)        = f (∈→ℕ v)
  foldTerm (ƛ b)          = foldTerm b
  foldTerm (f · x)        = foldTerm f ⊕ foldTerm x
  foldTerm (up t)         = foldTerm t
  foldTerm (down t)       = foldTerm t
  foldTerm (f ∙ x)        = foldTerm f ⊕ foldTerm x
  foldTerm (elim g f x t) = foldTerm g ⊕ foldTerm f ⊕ foldTerm x ⊕ foldTerm t
  foldTerm  z             = x
  foldTerm (s n)          = foldTerm n
  foldTerm (fold f x n)   = foldTerm f ⊕ foldTerm x ⊕ foldTerm n

⟦_⟧ᵗ : Type -> Set
⟦ σ ⇒ τ ⟧ᵗ = ⟦ σ ⟧ᵗ -> ⟦ τ ⟧ᵗ
⟦ □ σ   ⟧ᵗ = ⟦ σ ⟧ᵗ
⟦ nat   ⟧ᵗ = ℕ

data Env : Con -> Set where
  ø   : Env ε
  _▷_ : ∀ {Γ σ} -> Env Γ -> ⟦ σ ⟧ᵗ -> Env (Γ ▻ σ)

lookup : ∀ {Γ σ} -> σ ∈ Γ -> Env Γ -> ⟦ σ ⟧ᵗ
lookup  vz    (ρ ▷ x) = x
lookup (vs v) (ρ ▷ x) = lookup v ρ

mutual
  ⟦_⟧ : ∀ {Γ σ} -> Γ ⊢ σ -> Env Γ -> ⟦ σ ⟧ᵗ
  ⟦ var v        ⟧ ρ = lookup v ρ
  ⟦ ƛ b          ⟧ ρ = λ x -> ⟦ b ⟧ (ρ ▷ x)
  ⟦ f · x        ⟧ ρ = ⟦ f ⟧ ρ (⟦ x ⟧ ρ)
  ⟦ up t         ⟧ ρ = eval t
  ⟦ down t       ⟧ ρ = ⟦ t ⟧ ρ
  ⟦ f ∙ x        ⟧ ρ = ⟦ f ⟧ ρ (⟦ x ⟧ ρ)
  ⟦ elim g f x t ⟧ ρ = foldTerm (⟦ g ⟧ ρ) (⟦ f ⟧ ρ) (⟦ x ⟧ ρ) t
  ⟦ z            ⟧ ρ = 0
  ⟦ s n          ⟧ ρ = suc (⟦ n ⟧ ρ)
  ⟦ fold f x n   ⟧ ρ = Nat.fold (⟦ x ⟧ ρ) (⟦ f ⟧ ρ) (⟦ n ⟧ ρ)

  eval : ∀ {σ} -> Term σ -> ⟦ σ ⟧ᵗ
  eval t = ⟦ t ⟧ ø

Term⁺ : Type -> Set
Term⁺ σ = ∀ {Γ} -> Γ ⊢ σ

open import Relation.Binary.PropositionalEquality

I : ∀ {σ} -> Term⁺ (σ ⇒ σ)
I = ƛ var vz

A : ∀ {σ τ} -> Term⁺ ((σ ⇒ τ) ⇒ σ ⇒ τ)
A = ƛ ƛ var (vs vz) · var vz

plus : Term⁺ (nat ⇒ nat ⇒ nat)
plus = ƛ ƛ fold (ƛ s (var vz)) (var vz) (var (vs vz))

countVars : ∀ {σ} -> Term σ -> Term nat
countVars = elim plus (ƛ s z) z ∘ up

runCountVars : ∀ {σ} -> Term σ -> ℕ
runCountVars = eval ∘ countVars

testI : ∀ {σ} -> runCountVars (I {σ}) ≡ 1
testI = refl

testA : ∀ {σ τ} -> runCountVars (A {σ} {τ}) ≡ 2
testA = refl

testPlus : runCountVars plus ≡ 3
testPlus = refl

testCountVars : ∀ {σ t} -> runCountVars (countVars {σ} t) ≡ 3 + runCountVars t
testCountVars = refl
