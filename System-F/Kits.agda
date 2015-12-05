module System-F.Kits where

open import System-F.Prelude

module Context {α} (A : Set α) where
  infixl 5 _▻_

  data Con : Set α where
    ε   : Con
    _▻_ : Con -> A -> Con
    
module _ {α} {A : Set α} where
  infixl 5 _▻▻_
  infix  3 _⊆_ _∈_

  open Context A

  _▻▻_ : Con -> Con -> Con
  Γ ▻▻  ε      = Γ
  Γ ▻▻ (Δ ▻ τ) = Γ ▻▻ Δ ▻ τ

  data _⊆_ : Con -> Con -> Set where
    stop : ε ⊆ ε
    skip : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ     ⊆ Δ ▻ σ
    keep : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ▻ σ ⊆ Δ ▻ σ

  data _∈_ σ : Con -> Set where
    vz  : ∀ {Γ}   -> σ ∈ Γ ▻ σ
    vs_ : ∀ {Γ τ} -> σ ∈ Γ     -> σ ∈ Γ ▻ τ

  idˢ : ∀ {Γ} -> Γ ⊆ Γ
  idˢ {ε}     = stop
  idˢ {Γ ▻ σ} = keep idˢ

  _∘ˢ_ : ∀ {Γ Δ Ξ} -> Δ ⊆ Ξ -> Γ ⊆ Δ -> Γ ⊆ Ξ
  stop   ∘ˢ ι      = ι
  skip κ ∘ˢ ι      = skip (κ ∘ˢ ι)
  keep κ ∘ˢ skip ι = skip (κ ∘ˢ ι)
  keep κ ∘ˢ keep ι = keep (κ ∘ˢ ι)

  top : ∀ {Γ σ} -> Γ ⊆ Γ ▻ σ
  top = skip idˢ

  keeps : ∀ {Γ Δ} Ξ -> Γ ⊆ Δ -> Γ ▻▻ Ξ ⊆ Δ ▻▻ Ξ
  keeps  ε      ι = ι
  keeps (Ξ ▻ ν) ι = keep (keeps Ξ ι)

  renᵛ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> σ ∈ Γ -> σ ∈ Δ
  renᵛ  stop     ()
  renᵛ (skip ι)  v     = vs (renᵛ ι v)
  renᵛ (keep ι)  vz    = vz
  renᵛ (keep ι) (vs v) = vs (renᵛ ι v)

  idˢ-∘ˢ : ∀ {Γ Δ} -> (ι : Γ ⊆ Δ) -> idˢ ∘ˢ ι ≡ ι
  idˢ-∘ˢ  stop    = refl
  idˢ-∘ˢ (skip ι) = cong skip (idˢ-∘ˢ ι)
  idˢ-∘ˢ (keep ι) = cong keep (idˢ-∘ˢ ι)

  ∘ˢ-idˢ : ∀ {Γ Δ} -> (ι : Γ ⊆ Δ) -> ι ∘ˢ idˢ ≡ ι
  ∘ˢ-idˢ  stop    = refl
  ∘ˢ-idˢ (skip ι) = cong skip (∘ˢ-idˢ ι)
  ∘ˢ-idˢ (keep ι) = cong keep (∘ˢ-idˢ ι)

  renᵛ-idˢ : ∀ {Γ σ} (v : σ ∈ Γ)
           -> renᵛ idˢ v ≡ v
  renᵛ-idˢ  vz    = refl
  renᵛ-idˢ (vs v) = cong vs_ (renᵛ-idˢ v)

  renᵛ-∘ˢ : ∀ {Γ Δ Ξ σ} (κ : Δ ⊆ Ξ) (ι : Γ ⊆ Δ) (v : σ ∈ Γ)
          -> renᵛ κ (renᵛ ι v) ≡ renᵛ (κ ∘ˢ ι) v
  renᵛ-∘ˢ  stop     stop     ()
  renᵛ-∘ˢ (skip κ)  ι        v     = cong vs_ (renᵛ-∘ˢ κ ι v)
  renᵛ-∘ˢ (keep κ) (skip ι)  v     = cong vs_ (renᵛ-∘ˢ κ ι v)
  renᵛ-∘ˢ (keep κ) (keep ι)  vz    = refl
  renᵛ-∘ˢ (keep κ) (keep ι) (vs v) = cong vs_ (renᵛ-∘ˢ κ ι v)

open Context public

mapᶜ : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> Con A -> Con B
mapᶜ f  ε      = ε
mapᶜ f (Γ ▻ x) = mapᶜ f Γ ▻ f x

record Thing {α β} {A : Set α} (_∙_ : Con A -> A -> Set β) : Set (α ⊔ β) where
  field
    renᶠ    : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ∙ σ -> Δ ∙ σ
    renᶠ-∘ˢ : ∀ {Γ Δ Ξ σ} (κ : Δ ⊆ Ξ) (ι : Γ ⊆ Δ) (t : Γ ∙ σ)
            -> renᶠ κ (renᶠ ι t) ≡ renᶠ (κ ∘ˢ ι) t

  renᶜ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Con (Γ ∙ σ) -> Con (Δ ∙ σ)
  renᶜ ι = mapᶜ (renᶠ ι)

  renᶜ-⊆ : ∀ {Θ Ξ σ} {Γ Δ : Con (Θ ∙ σ)} -> (ι : Θ ⊆ Ξ) -> Γ ⊆ Δ -> renᶜ ι Γ ⊆ renᶜ ι Δ
  renᶜ-⊆ ι  stop    = stop
  renᶜ-⊆ ι (skip κ) = skip (renᶜ-⊆ ι κ)
  renᶜ-⊆ ι (keep κ) = keep (renᶜ-⊆ ι κ)

  shiftᶜ : ∀ {Γ σ τ} -> Con (Γ ∙ σ) -> Con ((Γ ▻ τ) ∙ σ)
  shiftᶜ = renᶜ top

  shiftᶜ-⊆ : ∀ {Θ σ τ} {Γ Δ : Con (Θ ∙ σ)} -> Γ ⊆ Δ -> shiftᶜ Γ ⊆ shiftᶜ Δ
  shiftᶜ-⊆ {τ = τ} = renᶜ-⊆ (top {σ = τ})

  renameᵛ : ∀ {Θ Ξ σ α} {Γ : Con (Θ ∙ σ)} -> (ι : Θ ⊆ Ξ) -> α ∈ Γ -> renᶠ ι α ∈ renᶜ ι Γ
  renameᵛ ι  vz    = vz
  renameᵛ ι (vs v) = vs (renameᵛ ι v)

  renᶜ-⊆-∘ˢ : ∀ {Θ Ξ σ} {Γ Δ Ω : Con (Θ ∙ σ)} (ι : Θ ⊆ Ξ) (ζ : Δ ⊆ Ω) (κ : Γ ⊆ Δ)
            -> renᶜ-⊆ ι ζ ∘ˢ renᶜ-⊆ ι κ ≡ renᶜ-⊆ ι (ζ ∘ˢ κ)
  renᶜ-⊆-∘ˢ ι  stop     stop    = refl
  renᶜ-⊆-∘ˢ ι (skip ζ)  κ       = cong skip (renᶜ-⊆-∘ˢ ι ζ κ)
  renᶜ-⊆-∘ˢ ι (keep ζ) (skip κ) = cong skip (renᶜ-⊆-∘ˢ ι ζ κ)
  renᶜ-⊆-∘ˢ ι (keep ζ) (keep κ) = cong keep (renᶜ-⊆-∘ˢ ι ζ κ)

  shiftᶜ-⊆-∘ˢ : ∀ {Θ σ τ} {Γ Δ Ω : Con (Θ ∙ σ)} (κ : Δ ⊆ Ω) (ι : Γ ⊆ Δ)
              -> (shiftᶜ-⊆ κ ∘ˢ shiftᶜ-⊆ ι) ≡ shiftᶜ-⊆ (κ ∘ˢ ι)
  shiftᶜ-⊆-∘ˢ {τ = τ} = renᶜ-⊆-∘ˢ (top {σ = τ})

  renᶜ-∘ˢ : ∀ {Θ Ξ Ω σ} (κ : Ξ ⊆ Ω) (ι : Θ ⊆ Ξ) (Γ : Con (Θ ∙ σ))
          -> renᶜ κ (renᶜ ι Γ) ≡ renᶜ (κ ∘ˢ ι) Γ
  renᶜ-∘ˢ κ ι  ε      = refl
  renᶜ-∘ˢ κ ι (Γ ▻ α) = cong₂ _▻_ (renᶜ-∘ˢ κ ι Γ) (renᶠ-∘ˢ κ ι α)

record Environment {α β} {A : Set α} {_∙_ : Con A -> A -> Set β}
                   (thing : Thing _∙_) : Set (α ⊔ β) where
  infix  3 _⊢ᵉ_
  infixl 5 _▷_ _▷▷_

  open Thing thing

  field
    varᶠ      : ∀ {Γ σ} -> σ ∈ Γ -> Γ ∙ σ
    renᶠ-varᶠ : ∀ {Γ Δ σ} (ι : Γ ⊆ Δ) (v : σ ∈ Γ)
              -> renᶠ ι (varᶠ v) ≡ varᶠ (renᵛ ι v)

  data _⊢ᵉ_ Δ : Con A -> Set β where
    Ø   : Δ ⊢ᵉ ε
    _▷_ : ∀ {Γ σ} -> Δ ⊢ᵉ Γ -> Δ ∙ σ -> Δ ⊢ᵉ Γ ▻ σ

  lookupᵉ : ∀ {Δ Γ σ} -> σ ∈ Γ -> Δ ⊢ᵉ Γ -> Δ ∙ σ
  lookupᵉ  vz    (ρ ▷ t) = t
  lookupᵉ (vs v) (ρ ▷ t) = lookupᵉ v ρ

  renᵉ : ∀ {Δ Ξ Γ} -> Δ ⊆ Ξ -> Δ ⊢ᵉ Γ -> Ξ ⊢ᵉ Γ
  renᵉ ι  Ø      = Ø
  renᵉ ι (ρ ▷ t) = renᵉ ι ρ ▷ renᶠ ι t

  keepᵉ : ∀ {Δ Γ σ} -> Δ ⊢ᵉ Γ -> Δ ▻ σ ⊢ᵉ Γ ▻ σ
  keepᵉ ρ = renᵉ top ρ ▷ varᶠ vz

  idᵉ : ∀ {Γ} -> Γ ⊢ᵉ Γ
  idᵉ {ε}     = Ø
  idᵉ {Γ ▻ σ} = keepᵉ idᵉ

  topᵉ : ∀ {Γ σ} -> Γ ∙ σ -> Γ ⊢ᵉ Γ ▻ σ
  topᵉ t = idᵉ ▷ t

  shiftᵉ : ∀ {Δ Γ τ} -> Δ ⊢ᵉ Γ -> Δ ▻ τ ⊢ᵉ Γ
  shiftᵉ = renᵉ top

  keepsᵉ : ∀ {Γ Δ} Ξ -> Δ ⊢ᵉ Γ -> Δ ▻▻ Ξ ⊢ᵉ Γ ▻▻ Ξ
  keepsᵉ  ε      ρ = ρ
  keepsᵉ (Ξ ▻ ν) ρ = keepᵉ (keepsᵉ Ξ ρ)

  _▷▷_ : ∀ {Ξ Γ Δ} -> Ξ ⊢ᵉ Γ -> Ξ ⊢ᵉ Δ -> Ξ ⊢ᵉ Γ ▻▻ Δ
  ρ ▷▷  Ø      = ρ
  ρ ▷▷ (η ▷ t) = ρ ▷▷ η ▷ t

  to-env : ∀ {Γ Δ} -> Γ ⊆ Δ -> Δ ⊢ᵉ Γ
  to-env  stop    = Ø
  to-env (skip ι) = shiftᵉ (to-env ι)
  to-env (keep ι) = keepᵉ (to-env ι)

  renᵉ-∘ˢ : ∀ {Θ Γ Δ Ξ} (κ : Δ ⊆ Ξ) (ι : Γ ⊆ Δ) (ρ : Γ ⊢ᵉ Θ)
          -> renᵉ κ (renᵉ ι ρ) ≡ renᵉ (κ ∘ˢ ι) ρ
  renᵉ-∘ˢ κ ι  Ø      = refl
  renᵉ-∘ˢ κ ι (ρ ▷ t) = cong₂ _▷_ (renᵉ-∘ˢ κ ι ρ) (renᶠ-∘ˢ κ ι t)

  lookupᵉ-renᵉ : ∀ {Γ Δ Ξ σ} (v : σ ∈ Γ) (ι : Δ ⊆ Ξ) (ρ : Δ ⊢ᵉ Γ) 
               -> lookupᵉ v (renᵉ ι ρ) ≡ renᶠ ι (lookupᵉ v ρ)
  lookupᵉ-renᵉ  vz    ι (ρ ▷ t) = refl
  lookupᵉ-renᵉ (vs v) ι (ρ ▷ t) = lookupᵉ-renᵉ v ι ρ

  lookupᵉ-idᵉ : ∀ {Γ σ} (v : σ ∈ Γ)
              -> lookupᵉ v idᵉ ≡ varᶠ v
  lookupᵉ-idᵉ  vz    = refl
  lookupᵉ-idᵉ (vs v) = trans (lookupᵉ-renᵉ v top idᵉ)
                             (trans (cong (renᶠ top) (lookupᵉ-idᵉ v))
                                    (trans (renᶠ-varᶠ top v)
                                           (cong (varᶠ ∘ vs_) (renᵛ-idˢ v))))

record NestedEnvironments {α β γ} {A : Set α} {_∙_ : Con A -> A -> Set β} {σ}
                          {_◆_ : ∀ {Θ} -> Con (Θ ∙ σ) -> Θ ∙ σ -> Set γ}
                          {thing₁ : Thing _∙_} {thing₂ : ∀ {Θ} -> Thing (_◆_ {Θ})}
                          (env₂ : ∀ {Θ} -> Environment (thing₂ {Θ}))
                          (env₁ : Environment thing₁) : Set (α ⊔ β ⊔ γ) where
  open Thing thing₁
    
  field
    renⁿᶠ : ∀ {Θ Ξ α} {Γ : Con (Θ ∙ σ)} -> (ι : Θ ⊆ Ξ) -> Γ ◆ α -> renᶜ ι Γ ◆ renᶠ ι α

  private open module Dummy {Θ} = Environment (env₂ {Θ})

  renᵉ-⊆ : ∀ {Θ Ξ} {Γ Δ : Con (Θ ∙ σ)}
         -> (ι : Θ ⊆ Ξ) -> Δ ⊢ᵉ Γ -> renᶜ ι Δ ⊢ᵉ renᶜ ι Γ
  renᵉ-⊆ ι  Ø      = Ø
  renᵉ-⊆ ι (ρ ▷ t) = renᵉ-⊆ ι ρ ▷ renⁿᶠ ι t

  shiftᵉ-⊆ : ∀ {Θ τ} {Γ Δ : Con (Θ ∙ σ)} -> Δ ⊢ᵉ Γ -> shiftᶜ Δ ⊢ᵉ shiftᶜ Γ
  shiftᵉ-⊆ {τ = τ} = renᵉ-⊆ (top {σ = τ})
