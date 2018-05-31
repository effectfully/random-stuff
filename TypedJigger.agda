infixr 5 _⇒_
infixl 6 _▻_
infix  3 _⊢_ _∈_ _⊑_
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

data _⊑_ Γ : Con -> Set where
  instance
    stop : Γ ⊑ Γ
    skip : ∀ {Δ σ} -> Γ ⊑ Δ -> Γ ⊑ Δ ▻ σ

fit : ∀ {Δ Γ σ} -> Γ ▻ σ ⊑ Δ -> σ ∈ Δ
fit  stop      = vz
fit (skip emb) = vs (fit emb)

lam : ∀ {Γ σ τ} -> ((∀ {Δ} {{_ : Γ ▻ σ ⊑ Δ}} -> Δ ⊢ σ) -> Γ ▻ σ ⊢ τ) -> Γ ⊢ σ ⇒ τ
lam k = ƛ k λ {{emb}} -> var (fit emb)



I : Term (⋆ ⇒ ⋆)
I = lam λ x -> x

K : Term (⋆ ⇒ ⋆ ⇒ ⋆)
K = lam λ x -> lam λ y -> x

A : Term ((⋆ ⇒ ⋆) ⇒ ⋆ ⇒ ⋆)
A = lam λ f -> lam λ x -> f · x

O : Term (((⋆ ⇒ ⋆) ⇒ ⋆) ⇒ (⋆ ⇒ ⋆) ⇒ ⋆)
O = lam λ g -> lam λ f -> f · (g · f)

O-η : Term (((⋆ ⇒ ⋆) ⇒ ⋆) ⇒ (⋆ ⇒ ⋆) ⇒ ⋆)
O-η = lam λ g -> lam λ f -> f · (g · lam λ x -> f · x)
