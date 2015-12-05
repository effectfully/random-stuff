module System-F.Core where

open import System-F.Prelude
open import System-F.Kits

infixr 6 _⇒_
infix  3 _⊢ᵗ_ _⊢_
infixl 6 _·ᵗ_ _·_
infixl 9 _[_]ᵗ _[_]
infixr 5 Λ_ ƛ_

data Kind : Set where
  ⋆   : Kind
  _⇒_ : Kind -> Kind -> Kind

Conᵏ = Con Kind

mutual
  Type : Conᵏ -> Set
  Type Θ = Θ ⊢ᵗ ⋆

  -- No type-level lambdas.
  data _⊢ᵗ_ Θ : Kind -> Set where
    Var  : ∀ {σ} -> σ ∈ Θ -> Θ ⊢ᵗ σ
    _·ᵗ_ : ∀ {σ τ} -> Θ ⊢ᵗ σ ⇒ τ -> Θ ⊢ᵗ σ -> Θ ⊢ᵗ τ
    _⇒_  : Type Θ -> Type Θ -> Type Θ
    π    : ∀ σ -> Type (Θ ▻ σ) -> Type Θ

Conᵗ : Conᵏ -> Set
Conᵗ = Con ∘ Type

renᵗ : ∀ {Θ Ξ σ} -> Θ ⊆ Ξ -> Θ ⊢ᵗ σ -> Ξ ⊢ᵗ σ
renᵗ ι (Var v)  = Var (renᵛ ι v)
renᵗ ι (f ·ᵗ α) = renᵗ ι f ·ᵗ renᵗ ι α
renᵗ ι (α ⇒ β)  = renᵗ ι α ⇒ renᵗ ι β
renᵗ ι (π σ α)  = π σ (renᵗ (keep ι) α)

renᵗ-∘ˢ : ∀ {Θ Ξ Ω σ} (κ : Ξ ⊆ Ω) (ι : Θ ⊆ Ξ) (α : Θ ⊢ᵗ σ)
        -> renᵗ κ (renᵗ ι α) ≡ renᵗ (κ ∘ˢ ι) α
renᵗ-∘ˢ κ ι (Var v)  = cong Var (renᵛ-∘ˢ κ ι v)
renᵗ-∘ˢ κ ι (f ·ᵗ α) = cong₂ _·ᵗ_ (renᵗ-∘ˢ κ ι f) (renᵗ-∘ˢ κ ι α)
renᵗ-∘ˢ κ ι (α ⇒ β)  = cong₂ _⇒_  (renᵗ-∘ˢ κ ι α) (renᵗ-∘ˢ κ ι β)
renᵗ-∘ˢ κ ι (π σ α)  = cong (π σ) (renᵗ-∘ˢ (keep κ) (keep ι) α)

TypeTh : Thing _⊢ᵗ_
TypeTh = record
  { renᶠ = renᵗ
  ; cohᶠ = renᵗ-∘ˢ
  }

TypeEnv : Environment TypeTh
TypeEnv = record
  { varᶠ = Var
  }

open module TypeThing       = Thing       TypeTh
open module TypeEnvironment = Environment TypeEnv

subᵗ : ∀ {Ξ Θ σ} -> Ξ ⊢ᵉ Θ -> Θ ⊢ᵗ σ -> Ξ ⊢ᵗ σ
subᵗ ρ (Var v)  = lookupᵉ v ρ
subᵗ ρ (f ·ᵗ α) = subᵗ ρ f ·ᵗ subᵗ ρ α
subᵗ ρ (α ⇒ β)  = subᵗ ρ α ⇒ subᵗ ρ β
subᵗ ρ (π σ α)  = π σ (subᵗ (keepᵉ ρ) α)

_[_]ᵗ : ∀ {Θ σ τ} -> Θ ▻ σ ⊢ᵗ τ -> Θ ⊢ᵗ σ -> Θ ⊢ᵗ τ
β [ α ]ᵗ = subᵗ (topᵉ α) β

data _⊢_ {Θ} Γ : Type Θ -> Set where
  var  : ∀ {α}   -> α ∈ Γ -> Γ ⊢ α
  Λ_   : ∀ {σ α} -> shiftᶜ Γ ⊢ α -> Γ ⊢ π σ α
  _[_] : ∀ {σ β} -> Γ ⊢ π σ β -> (α : Θ ⊢ᵗ σ) -> Γ ⊢ β [ α ]ᵗ
  ƛ_   : ∀ {α β} -> Γ ▻ α ⊢ β -> Γ ⊢ α ⇒ β
  _·_  : ∀ {α β} -> Γ ⊢ α ⇒ β -> Γ ⊢ α     -> Γ ⊢ β
  
Type⁺ : Set
Type⁺ = ∀ {Θ} -> Type Θ

Term⁺ : Type⁺ -> Set
Term⁺ α = ∀ {Θ} {Γ : Conᵗ Θ} -> Γ ⊢ α

coerceCon : ∀ {Θ Γ Δ} {α : Type Θ} -> Γ ≡ Δ -> Γ ⊢ α -> Δ ⊢ α
coerceCon refl = id

ren : ∀ {Θ Γ Δ} {α : Type Θ} -> Γ ⊆ Δ -> Γ ⊢ α -> Δ ⊢ α
ren ι (var v)   = var (renᵛ ι v)
ren ι (Λ b)     = Λ (ren (shiftᶜ-⊆ ι) b)
ren ι (f [ α ]) = ren ι f [ α ]
ren ι (ƛ b)     = ƛ (ren (keep ι) b)
ren ι (f · x)   = ren ι f · ren ι x

ren-∘ˢ : ∀ {Θ Γ Δ Ξ} {α : Type Θ} (κ : Δ ⊆ Ξ) (ι : Γ ⊆ Δ) (t : Γ ⊢ α)
       -> ren κ (ren ι t) ≡ ren (κ ∘ˢ ι) t
ren-∘ˢ κ ι (var v)   = cong var (renᵛ-∘ˢ κ ι v)
ren-∘ˢ κ ι (Λ b)     = cong Λ_ (trans (ren-∘ˢ (shiftᶜ-⊆ κ) (shiftᶜ-⊆ ι) b)
                                      (cong (flip ren b) (shiftᶜ-⊆-∘ˢ κ ι)))
ren-∘ˢ κ ι (f [ α ]) = cong _[ α ] (ren-∘ˢ κ ι f)
ren-∘ˢ κ ι (ƛ b)     = cong ƛ_ (ren-∘ˢ (keep κ) (keep ι) b)
ren-∘ˢ κ ι (f · x)   = cong₂ _·_ (ren-∘ˢ κ ι f) (ren-∘ˢ κ ι x)

TermTh : ∀ {Θ} -> Thing (_⊢_ {Θ})
TermTh = record
  { renᶠ = ren
  ; cohᶠ = ren-∘ˢ
  }

TermEnv : ∀ {Θ} -> Environment (TermTh {Θ})
TermEnv = record
  { varᶠ = var
  }

module TermThing       {Θ} = Thing       (TermTh  {Θ})
module TermEnvironment {Θ} = Environment (TermEnv {Θ})
