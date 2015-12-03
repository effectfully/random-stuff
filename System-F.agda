infixr 6 _⇒ᵏ_ _⇒_
infixl 5 _▻ᵏ_
infix  3 _⊆ᵏ_ _∈ᵗ_ _∈_ _⊢ᵗ_ _⊢ᵗᵉ_ _⊢_
infixl 6 _·ᵗ_ _·_
infixl 9 _[_]ᵗ _[_]
infixr 5 Λ_ ƛ_

data Kind : Set where
  ⋆    : Kind
  _⇒ᵏ_ : Kind -> Kind -> Kind

data Conᵏ : Set where
  εᵏ   : Conᵏ
  _▻ᵏ_ : Conᵏ -> Kind -> Conᵏ

data _⊆ᵏ_ : Conᵏ -> Conᵏ -> Set where
  stopᵏ : εᵏ ⊆ᵏ εᵏ
  skipᵏ : ∀ {Θ Ξ σ} -> Θ ⊆ᵏ Ξ -> Θ      ⊆ᵏ Ξ ▻ᵏ σ
  keepᵏ : ∀ {Θ Ξ σ} -> Θ ⊆ᵏ Ξ -> Θ ▻ᵏ σ ⊆ᵏ Ξ ▻ᵏ σ

data _∈ᵗ_ σ : Conᵏ -> Set where
  vzᵗ  : ∀ {Θ}   -> σ ∈ᵗ Θ ▻ᵏ σ
  vsᵗ_ : ∀ {Θ τ} -> σ ∈ᵗ Θ      -> σ ∈ᵗ Θ ▻ᵏ τ

mutual
  Type : Conᵏ -> Set
  Type Θ = Θ ⊢ᵗ ⋆

  -- No type-level lambdas.
  data _⊢ᵗ_ Θ : Kind -> Set where
    Var  : ∀ {σ} -> σ ∈ᵗ Θ -> Θ ⊢ᵗ σ
    _·ᵗ_ : ∀ {σ τ} -> Θ ⊢ᵗ σ ⇒ᵏ τ -> Θ ⊢ᵗ σ -> Θ ⊢ᵗ τ
    _⇒_  : Type Θ -> Type Θ -> Type Θ
    π    : ∀ σ -> Type (Θ ▻ᵏ σ) -> Type Θ

idᵏ : ∀ {Θ} -> Θ ⊆ᵏ Θ
idᵏ {εᵏ}     = stopᵏ
idᵏ {Θ ▻ᵏ σ} = keepᵏ idᵏ

topᵏ : ∀ {Θ σ} -> Θ ⊆ᵏ Θ ▻ᵏ σ
topᵏ = skipᵏ idᵏ

renᵗᵛ : ∀ {Θ Ξ σ} -> Θ ⊆ᵏ Ξ -> σ ∈ᵗ Θ -> σ ∈ᵗ Ξ
renᵗᵛ  stopᵏ     ()
renᵗᵛ (skipᵏ ι)  v      = vsᵗ (renᵗᵛ ι v)
renᵗᵛ (keepᵏ ι)  vzᵗ    = vzᵗ
renᵗᵛ (keepᵏ ι) (vsᵗ v) = vsᵗ (renᵗᵛ ι v)

renᵗ : ∀ {Θ Ξ σ} -> Θ ⊆ᵏ Ξ -> Θ ⊢ᵗ σ -> Ξ ⊢ᵗ σ
renᵗ ι (Var v)  = Var (renᵗᵛ ι v)
renᵗ ι (f ·ᵗ α) = renᵗ ι f ·ᵗ renᵗ ι α
renᵗ ι (α ⇒ β)  = renᵗ ι α ⇒ renᵗ ι β
renᵗ ι (π σ α)  = π σ (renᵗ (keepᵏ ι) α)

data _⊢ᵗᵉ_ Ξ : Conᵏ -> Set where
  Øᵗ   : Ξ ⊢ᵗᵉ εᵏ
  _▷ᵗ_ : ∀ {Θ σ} -> Ξ ⊢ᵗᵉ Θ -> Ξ ⊢ᵗ σ -> Ξ ⊢ᵗᵉ Θ ▻ᵏ σ

lookupᵗᵉ : ∀ {Ξ Θ σ} -> σ ∈ᵗ Θ -> Ξ ⊢ᵗᵉ Θ -> Ξ ⊢ᵗ σ
lookupᵗᵉ  vzᵗ    (ρ ▷ᵗ α) = α
lookupᵗᵉ (vsᵗ v) (ρ ▷ᵗ α) = lookupᵗᵉ v ρ

renᵗᵉ : ∀ {Ξ Ω Θ} -> Ξ ⊆ᵏ Ω -> Ξ ⊢ᵗᵉ Θ -> Ω ⊢ᵗᵉ Θ
renᵗᵉ ι  Øᵗ      = Øᵗ
renᵗᵉ ι (ρ ▷ᵗ α) = renᵗᵉ ι ρ ▷ᵗ renᵗ ι α

keepᵗᵉ : ∀ {Ξ Θ σ} -> Ξ ⊢ᵗᵉ Θ -> Ξ ▻ᵏ σ ⊢ᵗᵉ Θ ▻ᵏ σ
keepᵗᵉ ρ = renᵗᵉ topᵏ ρ ▷ᵗ Var vzᵗ

idᵗᵉ : ∀ {Θ} -> Θ ⊢ᵗᵉ Θ
idᵗᵉ {εᵏ}     = Øᵗ
idᵗᵉ {Θ ▻ᵏ σ} = keepᵗᵉ idᵗᵉ

topᵗᵉ : ∀ {Θ σ} -> Θ ⊢ᵗ σ -> Θ ⊢ᵗᵉ Θ ▻ᵏ σ
topᵗᵉ α = idᵗᵉ ▷ᵗ α

subᵗ : ∀ {Ξ Θ σ} -> Ξ ⊢ᵗᵉ Θ -> Θ ⊢ᵗ σ -> Ξ ⊢ᵗ σ
subᵗ ρ (Var v)  = lookupᵗᵉ v ρ
subᵗ ρ (f ·ᵗ α) = subᵗ ρ f ·ᵗ subᵗ ρ α
subᵗ ρ (α ⇒ β)  = subᵗ ρ α ⇒ subᵗ ρ β
subᵗ ρ (π σ α)  = π σ (subᵗ (keepᵗᵉ ρ) α)

_[_]ᵗ : ∀ {Θ σ τ} -> Θ ▻ᵏ σ ⊢ᵗ τ -> Θ ⊢ᵗ σ -> Θ ⊢ᵗ τ
β [ α ]ᵗ = subᵗ (topᵗᵉ α) β

data Con Θ : Set where
  ε   : Con Θ
  _▻_ : Con Θ -> Type Θ -> Con Θ

renᶜ : ∀ {Θ Ξ} -> Θ ⊆ᵏ Ξ -> Con Θ -> Con Ξ
renᶜ ι  ε      = ε
renᶜ ι (Γ ▻ α) = renᶜ ι Γ ▻ renᵗ ι α

shiftᶜ : ∀ {Θ σ} -> Con Θ -> Con (Θ ▻ᵏ σ)
shiftᶜ = renᶜ topᵏ

data _∈_ {Θ} α : Con Θ -> Set where
  vz  : ∀ {Γ}   -> α ∈ Γ ▻ α
  vs_ : ∀ {Γ β} -> α ∈ Γ     -> α ∈ Γ ▻ β

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
Iᵀ = π ⋆ (Var vzᵗ ⇒ Var vzᵗ)

I : Term⁺ Iᵀ
I = Λ ƛ (var vz)

I·I : Term⁺ Iᵀ
I·I = I [ Iᵀ ] · I

K : Term⁺ (π ⋆ (π ⋆ (Var (vsᵗ vzᵗ) ⇒ Var vzᵗ ⇒ Var (vsᵗ vzᵗ))))
K = Λ Λ ƛ ƛ var (vs vz)

S : Term⁺ (π ⋆ (π ⋆ (π ⋆
      (  (Var (vsᵗ vsᵗ vzᵗ) ⇒ Var (vsᵗ vzᵗ) ⇒ Var vzᵗ)
       ⇒ (Var (vsᵗ vsᵗ vzᵗ) ⇒ Var (vsᵗ vzᵗ))
       ⇒  Var (vsᵗ vsᵗ vzᵗ)
       ⇒  Var vzᵗ))))
S = Λ Λ Λ ƛ ƛ ƛ var (vs vs vz) · var vz · (var (vs vz) · var vz)

I′ : Term⁺ Iᵀ
I′ = Λ   S [ Var vzᵗ ] [ Var vzᵗ ⇒ Var vzᵗ ] [ Var vzᵗ ]
       · K [ Var vzᵗ ] [ Var vzᵗ ⇒ Var vzᵗ ]
       · K [ Var vzᵗ ] [ Var vzᵗ ]
