infixr 5 _⇒_
infixl 6 _▻_ _▻▻_
infix  3 _⊢_ _∈_
infixr 5 vs_
infixr 4 ƛ_
infixl 6 _·_

data Type : Set where
  ⋆   : Type
  _⇒_ : Type -> Type -> Type

-- Contexts are snoc-lists

data Con : Set where
  ε   : Con
  _▻_ : (Γ : Con) (τ : Type) -> Con

data _∈_ σ : Con -> Set where
  vz  : ∀ {Γ}   -> σ ∈ Γ ▻ σ
  vs_ : ∀ {Γ τ} -> σ ∈ Γ     -> σ ∈ Γ ▻ τ

data _⊢_ Γ : Type -> Set where
  var : ∀ {σ}   -> σ ∈ Γ     -> Γ ⊢ σ
  ƛ_  : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _·_ : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ      -> Γ ⊢ τ

Term : Type -> Set
Term σ = ε ⊢ σ

-- A cons that does not match on the context.
-- This is the main trick to make inference work.

cons : Type -> Con -> Con
cons σ Γ = init∘cons σ Γ ▻ last∘cons σ Γ
  where
    last∘cons : Type -> Con -> Type
    last∘cons σ  ε      = σ
    last∘cons σ (Γ ▻ τ) = τ

    init∘cons : Type -> Con -> Con
    init∘cons σ  ε      = ε
    init∘cons σ (Γ ▻ τ) = cons σ Γ

_▻▻_ : Con -> Con -> Con
ε     ▻▻ Δ = Δ
Γ ▻ σ ▻▻ Δ = Γ ▻▻ cons σ Δ
  -- Inference would be better with `(Γ ▻▻ init∘cons σ Δ) ▻ last∘cons σ Δ`,
  -- but then `init∘cons` must use something else than `cons`,
  -- and I can't figure out what it must use.

coe : ∀ {α Δ σ} (A : Con -> Set α) Γ -> A (Γ ▻▻ Δ ▻ σ) -> A (Γ ▻▻ (Δ ▻ σ))
coe A  ε      x = x
coe A (Γ ▻ τ) x = coe A Γ x

fit : ∀ {Δ σ} Γ -> σ ∈ Γ ▻▻ cons σ Δ
fit {ε}     Γ = coe (_ ∈_) Γ vz
fit {Δ ▻ τ} Γ = coe (_ ∈_) Γ (vs (fit Γ))

lam : ∀ {Γ σ τ} -> ((∀ {Δ} -> Γ ▻ σ ▻▻ Δ ⊢ σ) -> Γ ▻ σ ⊢ τ) -> Γ ⊢ σ ⇒ τ
lam {Γ} k = ƛ k (var (fit Γ))

I : Term (⋆ ⇒ ⋆)
I = lam λ x -> x

K : Term (⋆ ⇒ ⋆ ⇒ ⋆)
K = lam λ x -> lam λ y -> y

A : Term ((⋆ ⇒ ⋆) ⇒ ⋆ ⇒ ⋆)
A = lam λ f -> lam λ x -> f · x

O : Term (((⋆ ⇒ ⋆) ⇒ ⋆) ⇒ (⋆ ⇒ ⋆) ⇒ ⋆)
O = lam λ g -> lam λ f -> f · (g · f)

O-η : Term (((⋆ ⇒ ⋆) ⇒ ⋆) ⇒ (⋆ ⇒ ⋆) ⇒ ⋆)
O-η = lam λ g -> lam λ f -> f · (g · lam λ x -> f · x)
