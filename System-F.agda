open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Sum renaming (map to smap)
open import Data.Product

infixl 5 _▻ᵏ_
infix  3 _⊆ᵏ_ _∈ᵗ_ _∈_ _⊆²_ _[_⊢ᵗ_] _[_⊢ᵗᵉ_] _⊢_
infixr 6 _⇒_
infixl 7 _·_
infixl 9 _[_]ᵗ _[_]
infixr 5 Λ_ ƛ_

data Kind : Set where
  ⋆ : Kind

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
  Type : Conᵏ -> Conᵏ -> Set
  Type Θᶠ Θᵇ = Θᶠ [ Θᵇ ⊢ᵗ ⋆ ]

  data _[_⊢ᵗ_] Θᶠ : Conᵏ -> Kind -> Set where
    Varᶠ : ∀ {Θᵇ σ} -> σ ∈ᵗ Θᶠ -> Θᶠ [ Θᵇ ⊢ᵗ σ ]
    Varᵇ : ∀ {Θᵇ σ} -> σ ∈ᵗ Θᵇ -> Θᶠ [ Θᵇ ⊢ᵗ σ ]
    _⇒_  : ∀ {Θᵇ} -> Type Θᶠ Θᵇ -> Type Θᶠ Θᵇ -> Type Θᶠ Θᵇ
    π    : ∀ {Θᵇ} σ -> Type Θᶠ (Θᵇ ▻ᵏ σ) -> Type Θᶠ Θᵇ

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

-- We don't need OPEs here.
renᵗᶠ : ∀ {Θᶠ Ξᶠ Θᵇ σ} -> Θᶠ ⊆ᵏ Ξᶠ -> Θᶠ [ Θᵇ ⊢ᵗ σ ] -> Ξᶠ [ Θᵇ ⊢ᵗ σ ]
renᵗᶠ ι (Varᶠ v) = Varᶠ (renᵗᵛ ι v)
renᵗᶠ ι (Varᵇ v) = Varᵇ v
renᵗᶠ ι (α ⇒ β)  = renᵗᶠ ι α ⇒ renᵗᶠ ι β
renᵗᶠ ι (π σ α)  = π σ (renᵗᶠ ι α)

renᵗᵇ : ∀ {Θᶠ Θᵇ Ξᵇ σ} -> Θᵇ ⊆ᵏ Ξᵇ -> Θᶠ [ Θᵇ ⊢ᵗ σ ] -> Θᶠ [ Ξᵇ ⊢ᵗ σ ]
renᵗᵇ ι (Varᶠ v) = Varᶠ v
renᵗᵇ ι (Varᵇ v) = Varᵇ (renᵗᵛ ι v)
renᵗᵇ ι (α ⇒ β)  = renᵗᵇ ι α ⇒ renᵗᵇ ι β
renᵗᵇ ι (π σ α)  = π σ (renᵗᵇ (keepᵏ ι) α)

data _[_⊢ᵗᵉ_] Ξᶠ Ξᵇ : Conᵏ -> Set where
  Øᵗ   : Ξᶠ [ Ξᵇ ⊢ᵗᵉ εᵏ ]
  _▷ᵗ_ : ∀ {Θ σ} -> Ξᶠ [ Ξᵇ ⊢ᵗᵉ Θ ] -> Ξᶠ [ Ξᵇ ⊢ᵗ σ ] -> Ξᶠ [ Ξᵇ ⊢ᵗᵉ Θ ▻ᵏ σ ]

lookupᵗᵉ : ∀ {Ξᶠ Ξᵇ Θ σ} -> σ ∈ᵗ Θ -> Ξᶠ [ Ξᵇ ⊢ᵗᵉ Θ ] -> Ξᶠ [ Ξᵇ ⊢ᵗ σ ]
lookupᵗᵉ  vzᵗ    (ρ ▷ᵗ α) = α
lookupᵗᵉ (vsᵗ v) (ρ ▷ᵗ α) = lookupᵗᵉ v ρ

renᵗᶠᵉ : ∀ {Ξᶠ Ωᶠ Ξᵇ Θ} -> Ξᶠ ⊆ᵏ Ωᶠ -> Ξᶠ [ Ξᵇ ⊢ᵗᵉ Θ ] -> Ωᶠ [ Ξᵇ  ⊢ᵗᵉ Θ ]
renᵗᶠᵉ ι  Øᵗ      = Øᵗ
renᵗᶠᵉ ι (ρ ▷ᵗ α) = renᵗᶠᵉ ι ρ ▷ᵗ renᵗᶠ ι α

renᵗᵇᵉ : ∀ {Ξᶠ Ξᵇ Ωᵇ Θ} -> Ξᵇ ⊆ᵏ Ωᵇ -> Ξᶠ [ Ξᵇ ⊢ᵗᵉ Θ ] -> Ξᶠ [ Ωᵇ  ⊢ᵗᵉ Θ ]
renᵗᵇᵉ ι  Øᵗ      = Øᵗ
renᵗᵇᵉ ι (ρ ▷ᵗ α) = renᵗᵇᵉ ι ρ ▷ᵗ renᵗᵇ ι α

keepᵗᵇᵉ : ∀ {Ξᶠ Ξᵇ Θ σ} -> Ξᶠ [ Ξᵇ ⊢ᵗᵉ Θ ] -> Ξᶠ [ Ξᵇ ▻ᵏ σ ⊢ᵗᵉ Θ ▻ᵏ σ ]
keepᵗᵇᵉ ρ = renᵗᵇᵉ topᵏ ρ ▷ᵗ Varᵇ vzᵗ

idᵗᵉ : ∀ {Θᵇ Θᶠ} -> Θᶠ [ Θᵇ ⊢ᵗᵉ Θᵇ ]
idᵗᵉ {εᵏ}     = Øᵗ
idᵗᵉ {Θ ▻ᵏ σ} = keepᵗᵇᵉ idᵗᵉ

topᵗᵇᵉ : ∀ {Θᶠ Θᵇ σ} -> Θᶠ [ Θᵇ ⊢ᵗ σ ] -> Θᶠ [ Θᵇ ⊢ᵗᵉ Θᵇ ▻ᵏ σ ]
topᵗᵇᵉ α = idᵗᵉ ▷ᵗ α

subᵗᵇ : ∀ {Ξᶠ Ξᵇ Θ σ} -> Ξᶠ [ Ξᵇ ⊢ᵗᵉ Θ ] -> Ξᶠ [ Θ ⊢ᵗ σ ] -> Ξᶠ [ Ξᵇ ⊢ᵗ σ ]
subᵗᵇ ρ (Varᶠ v) = Varᶠ v
subᵗᵇ ρ (Varᵇ v) = lookupᵗᵉ v ρ
subᵗᵇ ρ (α ⇒ β)  = subᵗᵇ ρ α ⇒ subᵗᵇ ρ β
subᵗᵇ ρ (π σ α)  = π σ (subᵗᵇ (keepᵗᵇᵉ ρ) α)

_[_]ᵗ : ∀ {Θᶠ Θᵇ σ τ} -> Θᶠ [ Θᵇ ▻ᵏ σ ⊢ᵗ τ ] -> Θᶠ [ Θᵇ ⊢ᵗ σ ] -> Θᶠ [ Θᵇ ⊢ᵗ τ ]
β [ α ]ᵗ = subᵗᵇ (topᵗᵇᵉ α) β

data Con Θᶠ Θᵇ : Set where
  ε   : Con Θᶠ Θᵇ
  _▻_ : Con Θᶠ Θᵇ -> Type Θᶠ Θᵇ -> Con Θᶠ Θᵇ

mapᶜ : ∀ {Θᶠ Θᵇ Θᶠ′ Θᵇ′} -> (Type Θᶠ Θᵇ -> Type Θᶠ′ Θᵇ′) -> Con Θᶠ Θᵇ -> Con Θᶠ′ Θᵇ′ 
mapᶜ f  ε      = ε
mapᶜ f (Γ ▻ σ) = mapᶜ f Γ ▻ f σ

renᶜᶠ : ∀ {Θᶠ Ξᶠ Θᵇ} -> Θᶠ ⊆ᵏ Ξᶠ -> Con Θᶠ Θᵇ -> Con Ξᶠ Θᵇ
renᶜᶠ = mapᶜ ∘ renᵗᶠ

shiftᶜᶠ : ∀ {Θᶠ Θᵇ σ} -> Con Θᶠ Θᵇ -> Con (Θᶠ ▻ᵏ σ) Θᵇ
shiftᶜᶠ = renᶜᶠ topᵏ

data _⊆²_ : Conᵏ × Conᵏ -> Conᵏ × Conᵏ -> Set where
  stop² : ∀ {Θ Ξ}           -> Θ  , Ξ  ⊆² Θ  , Ξ
  skip² : ∀ {Θ₀ Θ₁ Ξ₀ Ξ₁ σ} -> Θ₀ , Ξ₀ ⊆² Θ₁ , Ξ₁ -> Θ₀ , Ξ₀      ⊆² Θ₁ ▻ᵏ σ , Ξ₁ ▻ᵏ σ
  keep² : ∀ {Θ₀ Θ₁ Ξ₀ Ξ₁ σ} -> Θ₀ , Ξ₀ ⊆² Θ₁ , Ξ₁ -> Θ₀ , Ξ₀ ▻ᵏ σ ⊆² Θ₁      , Ξ₁ ▻ᵏ σ

freeʳ : ∀ {Θᶠ Θᵇ Ξᶠ Ξᵇ} -> Θᶠ , Θᵇ ⊆² Ξᶠ , Ξᵇ -> Θᶠ ⊆ᵏ Ξᶠ
freeʳ  stop²    = idᵏ
freeʳ (skip² ι) = skipᵏ (freeʳ ι)
freeʳ (keep² ι) = freeʳ ι

openᵗᵛ : ∀ {Θᶠ Θᵇ Ξᶠ Ξᵇ σ} -> Θᶠ , Θᵇ ⊆² Ξᶠ , Ξᵇ -> σ ∈ᵗ Ξᵇ -> σ ∈ᵗ Θᵇ ⊎ σ ∈ᵗ Ξᶠ
openᵗᵛ  stop²     v      = inj₁ v
openᵗᵛ (skip² ι)  vzᵗ    = inj₂ vzᵗ
openᵗᵛ (skip² ι) (vsᵗ v) = smap id vsᵗ_ (openᵗᵛ ι v)
openᵗᵛ (keep² ι)  vzᵗ    = inj₁ vzᵗ
openᵗᵛ (keep² ι) (vsᵗ v) = smap vsᵗ_ id (openᵗᵛ ι v)

openᵗ : ∀ {Θᶠ Θᵇ Ξᶠ Ξᵇ σ} -> Θᶠ , Θᵇ ⊆² Ξᶠ , Ξᵇ -> Θᶠ [ Ξᵇ ⊢ᵗ σ ] -> Ξᶠ [ Θᵇ ⊢ᵗ σ ]
openᵗ ι (Varᶠ v) = Varᶠ (renᵗᵛ (freeʳ ι) v)
openᵗ ι (Varᵇ v) = [ Varᵇ , Varᶠ ]′ (openᵗᵛ ι v)
openᵗ ι (α ⇒ β)  = openᵗ ι α ⇒ openᵗ ι β
openᵗ ι (π σ α)  = π σ (openᵗ (keep² ι) α)

open₁ : ∀ {Θᶠ Θᵇ σ τ} -> Θᶠ [ Θᵇ ▻ᵏ σ ⊢ᵗ τ ] -> Θᶠ ▻ᵏ σ [ Θᵇ ⊢ᵗ τ ]
open₁ = openᵗ (skip² stop²)

data _∈_ {Θᶠ Θᵇ} α : Con Θᶠ Θᵇ -> Set where
  vz  : ∀ {Γ}   -> α ∈ Γ ▻ α
  vs_ : ∀ {Γ β} -> α ∈ Γ     -> α ∈ Γ ▻ β

data _⊢_ {Θᶠ Θᵇ} Γ : Type Θᶠ Θᵇ -> Set where
  var  : ∀ {α}   -> α ∈ Γ -> Γ ⊢ α
  Λ_   : ∀ {σ α} -> shiftᶜᶠ Γ ⊢ open₁ α -> Γ ⊢ π σ α
  _[_] : ∀ {σ β} -> Γ ⊢ π σ β -> (α : Θᶠ [ Θᵇ ⊢ᵗ σ ]) -> Γ ⊢ β [ α ]ᵗ
  ƛ_   : ∀ {α β} -> Γ ▻ α ⊢ β -> Γ ⊢ α ⇒ β
  _·_  : ∀ {α β} -> Γ ⊢ α ⇒ β -> Γ ⊢ α     -> Γ ⊢ β

Type⁺ : Set
Type⁺ = ∀ {Θᶠ Θᵇ} -> Type Θᶠ Θᵇ

Term⁺ : Type⁺ -> Set
Term⁺ α = ∀ {Θᶠ Θᵇ} {Γ : Con Θᶠ Θᵇ} -> Γ ⊢ α

Iᵀ : Type⁺
Iᵀ = π ⋆ (Varᵇ vzᵗ ⇒ Varᵇ vzᵗ)

I : Term⁺ Iᵀ
I = Λ ƛ (var vz)

I·I : Term⁺ Iᵀ
I·I = I [ Iᵀ ] · I

K : Term⁺ (π ⋆ (π ⋆ (Varᵇ (vsᵗ vzᵗ) ⇒ Varᵇ vzᵗ ⇒ Varᵇ (vsᵗ vzᵗ))))
K = Λ Λ ƛ ƛ var (vs vz)

S : Term⁺ (π ⋆ (π ⋆ (π ⋆
      (  (Varᵇ (vsᵗ vsᵗ vzᵗ) ⇒ Varᵇ (vsᵗ vzᵗ) ⇒ Varᵇ vzᵗ)
       ⇒ (Varᵇ (vsᵗ vsᵗ vzᵗ) ⇒ Varᵇ (vsᵗ vzᵗ))
       ⇒  Varᵇ (vsᵗ vsᵗ vzᵗ)
       ⇒  Varᵇ vzᵗ))))
S = Λ Λ Λ ƛ ƛ ƛ var (vs vs vz) · var vz · (var (vs vz) · var vz)

I′ : Term⁺ Iᵀ
I′ = Λ   S [ Varᶠ vzᵗ ] [ Varᶠ vzᵗ ⇒ Varᶠ vzᵗ ] [ Varᶠ vzᵗ ]
       · K [ Varᶠ vzᵗ ] [ Varᶠ vzᵗ ⇒ Varᶠ vzᵗ ]
       · K [ Varᶠ vzᵗ ] [ Varᶠ vzᵗ ]
