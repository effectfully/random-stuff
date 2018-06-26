infixr 5 _⇒_
infixl 6 _▻_ _▻▻_
infix  3 _⊢_ _∈_
infixr 5 vs_
infixr 4 ƛ_
infixl 6 _·_

data Type : Set where
  ⋆   : Type
  _⇒_ : Type -> Type -> Type

data Con : Set where
  ε   : Con
  _▻_ : Con -> Type -> Con

data _∈_ σ : Con -> Set where
  vz  : ∀ {Γ}   -> σ ∈ Γ ▻ σ
  vs_ : ∀ {Γ τ} -> σ ∈ Γ     -> σ ∈ Γ ▻ τ

data _⊢_ Γ : Type -> Set where
  var : ∀ {σ}   -> σ ∈ Γ     -> Γ ⊢ σ
  ƛ_  : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _·_ : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ      -> Γ ⊢ τ

Term : Type -> Set
Term σ = ε ⊢ σ

lastDef : Type -> Con -> Type
lastDef σ  ε      = σ
lastDef σ (Γ ▻ τ) = τ

mutual
  cons : Type -> Con -> Con
  cons σ Γ = shift σ Γ ▻ lastDef σ Γ

  shift : Type -> Con -> Con
  shift σ  ε      = ε
  shift σ (Γ ▻ τ) = cons σ Γ

_▻▻_ : Con -> Con -> Con
ε     ▻▻ Δ = Δ
Γ ▻ σ ▻▻ Δ = Γ ▻▻ cons σ Δ -- Inference would be better with `Γ ▻▻ shift σ Δ ▻ lastDef σ Δ`,
                           -- but then `shift` must use something else than `cons`,
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
