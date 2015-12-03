open import Level

infixr 6 _⇒_
infix  3 _⊢ᵗ_ _⊢_
infixl 6 _·ᵗ_ _·_
infixl 9 _[_]ᵗ _[_]
infixr 5 Λ_ ƛ_

module Context {α} (A : Set α) where
  infixl 5 _▻_

  data Con : Set α where
    ε   : Con
    _▻_ : Con -> A -> Con

module _ where
  open Context

  mapᶜ : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> Con A -> Con B
  mapᶜ f  ε      = ε
  mapᶜ f (Γ ▻ x) = mapᶜ f Γ ▻ f x

module _ {α} {A : Set α} where
  infix 3 _⊆_ _∈_

  open Context A

  data _⊆_ : Con -> Con -> Set where
    stop : ε ⊆ ε
    skip : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ     ⊆ Δ ▻ σ
    keep : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ▻ σ ⊆ Δ ▻ σ

  data _∈_ σ : Con -> Set where
    vz  : ∀ {Γ}   -> σ ∈ Γ ▻ σ
    vs_ : ∀ {Γ τ} -> σ ∈ Γ     -> σ ∈ Γ ▻ τ

  id : ∀ {Γ} -> Γ ⊆ Γ
  id {ε}     = stop
  id {Γ ▻ σ} = keep id

  top : ∀ {Γ σ} -> Γ ⊆ Γ ▻ σ
  top = skip id

  renᵛ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> σ ∈ Γ -> σ ∈ Δ
  renᵛ  stop     ()
  renᵛ (skip ι)  v     = vs (renᵛ ι v)
  renᵛ (keep ι)  vz    = vz
  renᵛ (keep ι) (vs v) = vs (renᵛ ι v)

  record Environment {β} (_∙_ : Con -> A -> Set β) : Set (α ⊔ β) where
    infix 3 _⊢ᵉ_

    field
      renᶠ   : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ∙ σ -> Δ ∙ σ
      freshᶠ : ∀ {Γ σ} -> (Γ ▻ σ) ∙ σ

    data _⊢ᵉ_ Δ : Con -> Set β where
      Ø   : Δ ⊢ᵉ ε
      _▷_ : ∀ {Γ σ} -> Δ ⊢ᵉ Γ -> Δ ∙ σ -> Δ ⊢ᵉ Γ ▻ σ

    lookupᵉ : ∀ {Δ Γ σ} -> σ ∈ Γ -> Δ ⊢ᵉ Γ -> Δ ∙ σ
    lookupᵉ  vz    (ρ ▷ t) = t
    lookupᵉ (vs v) (ρ ▷ t) = lookupᵉ v ρ

    renᵉ : ∀ {Δ Ξ Γ} -> Δ ⊆ Ξ -> Δ ⊢ᵉ Γ -> Ξ ⊢ᵉ Γ
    renᵉ ι  Ø      = Ø
    renᵉ ι (ρ ▷ t) = renᵉ ι ρ ▷ renᶠ ι t

    keepᵉ : ∀ {Δ Γ σ} -> Δ ⊢ᵉ Γ -> Δ ▻ σ ⊢ᵉ Γ ▻ σ
    keepᵉ ρ = renᵉ top ρ ▷ freshᶠ

    idᵉ : ∀ {Γ} -> Γ ⊢ᵉ Γ
    idᵉ {ε}     = Ø
    idᵉ {Γ ▻ σ} = keepᵉ idᵉ

    topᵉ : ∀ {Γ σ} -> Γ ∙ σ -> Γ ⊢ᵉ Γ ▻ σ
    topᵉ t = idᵉ ▷ t

data Kind : Set where
  ⋆   : Kind
  _⇒_ : Kind -> Kind -> Kind

open Context Kind renaming (Con to KindCon; ε to ε̂ᵏ; _▻_ to _▻ᵏ_)

mutual
  Type : KindCon -> Set
  Type Θ = Θ ⊢ᵗ ⋆

  -- No type-level lambdas.
  data _⊢ᵗ_ Θ : Kind -> Set where
    Var  : ∀ {σ} -> σ ∈ Θ -> Θ ⊢ᵗ σ
    _·ᵗ_ : ∀ {σ τ} -> Θ ⊢ᵗ σ ⇒ τ -> Θ ⊢ᵗ σ -> Θ ⊢ᵗ τ
    _⇒_  : Type Θ -> Type Θ -> Type Θ
    π    : ∀ σ -> Type (Θ ▻ᵏ σ) -> Type Θ

renᵗ : ∀ {Θ Ξ σ} -> Θ ⊆ Ξ -> Θ ⊢ᵗ σ -> Ξ ⊢ᵗ σ
renᵗ ι (Var v)  = Var (renᵛ ι v)
renᵗ ι (f ·ᵗ α) = renᵗ ι f ·ᵗ renᵗ ι α
renᵗ ι (α ⇒ β)  = renᵗ ι α ⇒ renᵗ ι β
renᵗ ι (π σ α)  = π σ (renᵗ (keep ι) α)

shiftᵗ : ∀ {Θ σ τ} -> Θ ⊢ᵗ σ -> Θ ▻ᵏ τ ⊢ᵗ σ
shiftᵗ = renᵗ top

open Environment record
  { renᶠ   = renᵗ
  ; freshᶠ = Var vz
  }

subᵗ : ∀ {Ξ Θ σ} -> Ξ ⊢ᵉ Θ -> Θ ⊢ᵗ σ -> Ξ ⊢ᵗ σ
subᵗ ρ (Var v)  = lookupᵉ v ρ
subᵗ ρ (f ·ᵗ α) = subᵗ ρ f ·ᵗ subᵗ ρ α
subᵗ ρ (α ⇒ β)  = subᵗ ρ α ⇒ subᵗ ρ β
subᵗ ρ (π σ α)  = π σ (subᵗ (keepᵉ ρ) α)

_[_]ᵗ : ∀ {Θ σ τ} -> Θ ▻ᵏ σ ⊢ᵗ τ -> Θ ⊢ᵗ σ -> Θ ⊢ᵗ τ
β [ α ]ᵗ = subᵗ (topᵉ α) β

open module TypeCon Θ = Context (Type Θ)

shiftᶜ : ∀ {Θ σ} -> Con Θ -> Con (Θ ▻ᵏ σ)
shiftᶜ = mapᶜ shiftᵗ

data _⊢_ {Θ} Γ : Type Θ -> Set where
  var  : ∀ {α}   -> α ∈ Γ -> Γ ⊢ α
  Λ_   : ∀ {σ α} -> shiftᶜ Γ ⊢ α -> Γ ⊢ π σ α
  _[_] : ∀ {σ β} -> Γ ⊢ π σ β -> (α : Θ ⊢ᵗ σ) -> Γ ⊢ β [ α ]ᵗ
  ƛ_   : ∀ {α β} -> Γ ▻ α ⊢ β -> Γ ⊢ α ⇒ β
  _·_  : ∀ {α β} -> Γ ⊢ α ⇒ β -> Γ ⊢ α     -> Γ ⊢ β
  
Type⁺ : Set
Type⁺ = ∀ {Θ} -> Type Θ

Term⁺ : Type⁺ -> Set
Term⁺ α = ∀ {Θ} {Γ : Con Θ} -> Γ ⊢ α

Iᵀ : Type⁺
Iᵀ = π ⋆ (Var vz ⇒ Var vz)

I : Term⁺ Iᵀ
I = Λ ƛ var vz

I·I : Term⁺ Iᵀ
I·I = I [ Iᵀ ] · I

K : Term⁺ (π ⋆ (π ⋆ (Var (vs vz) ⇒ Var vz ⇒ Var (vs vz))))
K = Λ Λ ƛ ƛ var (vs vz)

S : Term⁺ (π ⋆ (π ⋆ (π ⋆
      (  (Var (vs vs vz) ⇒ Var (vs vz) ⇒ Var vz)
       ⇒ (Var (vs vs vz) ⇒ Var (vs vz))
       ⇒  Var (vs vs vz)
       ⇒  Var vz))))
S = Λ Λ Λ ƛ ƛ ƛ var (vs vs vz) · var vz · (var (vs vz) · var vz)

I′ : Term⁺ Iᵀ
I′ = Λ   S [ Var vz ] [ Var vz ⇒ Var vz ] [ Var vz ]
       · K [ Var vz ] [ Var vz ⇒ Var vz ]
       · K [ Var vz ] [ Var vz ]
