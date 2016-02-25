open import Function
open import Data.Empty
open import Data.Sum

infixl 5 _▻_
infixr 6 _⇒_
infix  4 _⊆_ _∈_ _⊢_ _⊢ⁿᵉ_ _⊢ⁿᶠ_ _⊨_ _⊨*_
infix  4 vs_
infixr 3 ƛ_ ƛⁿᶠ_
infixl 6 _·_ _·ⁿᵉ_

data Type : Set where
  ⋆   : Type
  _⇒_ : Type -> Type -> Type

data Con : Set where
  ε   : Con
  _▻_ : Con -> Type -> Con

data _⊆_ : Con -> Con -> Set where
  stop : ∀ {Γ}     -> Γ ⊆ Γ
  skip : ∀ {Γ Δ τ} -> Γ ⊆ Δ -> Γ     ⊆ Δ ▻ τ
  keep : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ▻ σ ⊆ Δ ▻ σ

data _∈_ σ : Con -> Set where
  vz  : ∀ {Γ}   -> σ ∈ Γ ▻ σ
  vs_ : ∀ {Γ τ} -> σ ∈ Γ     -> σ ∈ Γ ▻ τ 

data _⊢_ Γ : Type -> Set where
  var : ∀ {σ}   -> σ ∈ Γ     -> Γ ⊢ σ
  ƛ_  : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _·_ : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ

mutual
  data _⊢ⁿᵉ_ Γ : Type -> Set where
    varⁿᵉ : ∀ {σ}   -> σ ∈ Γ       -> Γ ⊢ⁿᵉ σ
    _·ⁿᵉ_ : ∀ {σ τ} -> Γ ⊢ⁿᵉ σ ⇒ τ -> Γ ⊢ⁿᶠ σ -> Γ ⊢ⁿᵉ τ

  data _⊢ⁿᶠ_ Γ : Type -> Set where
    neⁿᶠ : ∀ {σ}   -> Γ ⊢ⁿᵉ σ     -> Γ ⊢ⁿᶠ σ
    ƛⁿᶠ_ : ∀ {σ τ} -> Γ ▻ σ ⊢ⁿᶠ τ -> Γ ⊢ⁿᶠ σ ⇒ τ

top : ∀ {Γ σ} -> Γ ⊆ Γ ▻ σ
top = skip stop

_∘ˢ_ : ∀ {Γ Δ Θ} -> Δ ⊆ Θ -> Γ ⊆ Δ -> Γ ⊆ Θ
stop   ∘ˢ ψ      = ψ
skip φ ∘ˢ ψ      = skip (φ ∘ˢ ψ)
keep φ ∘ˢ stop   = keep  φ
keep φ ∘ˢ skip ψ = skip (φ ∘ˢ ψ)
keep φ ∘ˢ keep ψ = keep (φ ∘ˢ ψ)

renᵛ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> σ ∈ Γ -> σ ∈ Δ
renᵛ  stop     v     = v
renᵛ (skip ψ)  v     = vs (renᵛ ψ v)
renᵛ (keep ψ)  vz    = vz
renᵛ (keep ψ) (vs v) = vs (renᵛ ψ v)

mutual
  embⁿᵉ : ∀ {Γ σ} -> Γ ⊢ⁿᵉ σ -> Γ ⊢ σ
  embⁿᵉ (varⁿᵉ v) = var v
  embⁿᵉ (f ·ⁿᵉ x) = embⁿᵉ f · embⁿᶠ x

  embⁿᶠ : ∀ {Γ σ} -> Γ ⊢ⁿᶠ σ -> Γ ⊢ σ
  embⁿᶠ (neⁿᶠ n) = embⁿᵉ n
  embⁿᶠ (ƛⁿᶠ b)  = ƛ (embⁿᶠ b)

mutual
  renⁿᵉ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ⁿᵉ σ -> Δ ⊢ⁿᵉ σ
  renⁿᵉ ψ (varⁿᵉ v) = varⁿᵉ (renᵛ ψ v)
  renⁿᵉ ψ (f ·ⁿᵉ x) = renⁿᵉ ψ f ·ⁿᵉ renⁿᶠ ψ x

  renⁿᶠ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ⁿᶠ σ -> Δ ⊢ⁿᶠ σ
  renⁿᶠ ψ (neⁿᶠ n) = neⁿᶠ (renⁿᵉ ψ n)
  renⁿᶠ ψ (ƛⁿᶠ b)  = ƛⁿᶠ (renⁿᶠ (keep ψ) b)

mutual
  _⊨_ : Con -> Type -> Set
  Γ ⊨ σ = Γ ⊢ⁿᵉ σ ⊎ Kripke Γ σ

  Kripke : Con -> Type -> Set
  Kripke Γ  ⋆      = ⊥
  Kripke Γ (σ ⇒ τ) = ∀ {Δ} -> Γ ⊆ Δ -> Δ ⊨ σ -> Δ ⊨ τ

varˢ : ∀ {Γ σ} -> σ ∈ Γ -> Γ ⊨ σ
varˢ = inj₁ ∘ varⁿᵉ

renˢ : ∀ {σ Γ Δ} -> Γ ⊆ Δ -> Γ ⊨ σ -> Δ ⊨ σ
renˢ         ψ (inj₁ t)  = inj₁ (renⁿᵉ ψ t)
renˢ {⋆}     ψ (inj₂ ())
renˢ {σ ⇒ τ} ψ (inj₂ k)  = inj₂ (λ φ -> k (φ ∘ˢ ψ))

readback : ∀ {σ Γ} -> Γ ⊨ σ -> Γ ⊢ⁿᶠ σ
readback         (inj₁ t)  = neⁿᶠ t
readback {⋆}     (inj₂ ())
readback {σ ⇒ τ} (inj₂ k)  = ƛⁿᶠ (readback (k top (varˢ vz)))

_∙_ : ∀ {Γ σ τ} -> Γ ⊨ σ ⇒ τ -> Γ ⊨ σ -> Γ ⊨ τ
inj₁ f ∙ x = inj₁ (f ·ⁿᵉ readback x)
inj₂ k ∙ x = k stop x

data _⊨*_ Δ : Con -> Set where
  Ø   : Δ ⊨* ε
  _▷_ : ∀ {Γ σ} -> Δ ⊨* Γ -> Δ ⊨ σ -> Δ ⊨* Γ ▻ σ

lookupᵉ : ∀ {Γ Δ σ} -> σ ∈ Γ -> Δ ⊨* Γ -> Δ ⊨ σ
lookupᵉ  vz    (ρ ▷ x) = x
lookupᵉ (vs v) (ρ ▷ x) = lookupᵉ v ρ

idᵉ : ∀ {Γ} -> Γ ⊨* Γ
idᵉ {ε}     = Ø
idᵉ {Γ ▻ σ} = renᵉ top idᵉ ▷ varˢ vz

renᵉ : ∀ {Γ Δ Θ} -> Δ ⊆ Θ -> Δ ⊨* Γ -> Θ ⊨* Γ
renᵉ ψ  Ø      = Ø
renᵉ ψ (ρ ▷ x) = renᵉ ψ ρ ▷ renˢ ψ x

⟦_⟧ : ∀ {Γ Δ τ} -> Γ ⊢ τ -> Δ ⊨* Γ -> Δ ⊨ τ
⟦ var v ⟧ ρ = lookupᵉ v ρ
⟦ ƛ b   ⟧ ρ = inj₂ (λ ψ x -> ⟦ b ⟧ (renᵉ ψ ρ ▷ x))
⟦ f · x ⟧ ρ = ⟦ f ⟧ ρ ∙ ⟦ x ⟧ ρ

eval : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊨ σ
eval t = ⟦ t ⟧ idᵉ

norm : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢ σ
norm = embⁿᶠ ∘ readback ∘ eval
