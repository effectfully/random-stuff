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
    list : Θ ⊢ᵗ ⋆ ⇒ ⋆

Conᵗ : Conᵏ -> Set
Conᵗ = Con ∘ Type

renᵗ : ∀ {Θ Ξ σ} -> Θ ⊆ Ξ -> Θ ⊢ᵗ σ -> Ξ ⊢ᵗ σ
renᵗ ι (Var v)  = Var (renᵛ ι v)
renᵗ ι (f ·ᵗ α) = renᵗ ι f ·ᵗ renᵗ ι α
renᵗ ι (α ⇒ β)  = renᵗ ι α ⇒ renᵗ ι β
renᵗ ι (π σ β)  = π σ (renᵗ (keep ι) β)
renᵗ ι  list    = list

shiftᵗ : ∀ {Θ σ τ} -> Θ ⊢ᵗ σ -> Θ ▻ τ ⊢ᵗ σ
shiftᵗ = renᵗ top

renᵗ-∘ˢ : ∀ {Θ Ξ Ω σ} (κ : Ξ ⊆ Ω) (ι : Θ ⊆ Ξ) (α : Θ ⊢ᵗ σ)
        -> renᵗ κ (renᵗ ι α) ≡ renᵗ (κ ∘ˢ ι) α
renᵗ-∘ˢ κ ι (Var v)  = cong Var (renᵛ-∘ˢ κ ι v)
renᵗ-∘ˢ κ ι (f ·ᵗ α) = cong₂ _·ᵗ_ (renᵗ-∘ˢ κ ι f) (renᵗ-∘ˢ κ ι α)
renᵗ-∘ˢ κ ι (α ⇒ β)  = cong₂ _⇒_  (renᵗ-∘ˢ κ ι α) (renᵗ-∘ˢ κ ι β)
renᵗ-∘ˢ κ ι (π σ β)  = cong (π σ) (renᵗ-∘ˢ (keep κ) (keep ι) β)
renᵗ-∘ˢ κ ι  list    = refl

TypeTh : Thing _⊢ᵗ_
TypeTh = record
  { renᶠ    = renᵗ
  ; renᶠ-∘ˢ = renᵗ-∘ˢ
  }

TypeEnv : Environment TypeTh
TypeEnv = record
  { varᶠ      = Var
  ; renᶠ-varᶠ = λ ι v -> refl
  }

open module TypeThing       = Thing       TypeTh
open module TypeEnvironment = Environment TypeEnv

subᵗ : ∀ {Ξ Θ σ} -> Ξ ⊢ᵉ Θ -> Θ ⊢ᵗ σ -> Ξ ⊢ᵗ σ
subᵗ ρ (Var v)  = lookupᵉ v ρ
subᵗ ρ (f ·ᵗ α) = subᵗ ρ f ·ᵗ subᵗ ρ α
subᵗ ρ (α ⇒ β)  = subᵗ ρ α ⇒ subᵗ ρ β
subᵗ ρ (π σ β)  = π σ (subᵗ (keepᵉ ρ) β)
subᵗ ρ  list    = list

_[_]ᵗ : ∀ {Θ σ τ} -> Θ ▻ σ ⊢ᵗ τ -> Θ ⊢ᵗ σ -> Θ ⊢ᵗ τ
β [ α ]ᵗ = subᵗ (topᵉ α) β

data _⊢_ {Θ} Γ : Type Θ -> Set where
  var   : ∀ {α}   -> α ∈ Γ -> Γ ⊢ α
  Λ_    : ∀ {σ β} -> shiftᶜ Γ ⊢ β -> Γ ⊢ π σ β
  _[_]  : ∀ {σ β} -> Γ ⊢ π σ β -> (α : Θ ⊢ᵗ σ) -> Γ ⊢ β [ α ]ᵗ
  ƛ_    : ∀ {α β} -> Γ ▻ α ⊢ β -> Γ ⊢ α ⇒ β
  _·_   : ∀ {α β} -> Γ ⊢ α ⇒ β -> Γ ⊢ α     -> Γ ⊢ β
  []    : ∀ {α}   -> Γ ⊢ list ·ᵗ α
  _::_  : ∀ {α}   -> Γ ⊢ α -> Γ ⊢ list ·ᵗ α -> Γ ⊢ list ·ᵗ α
  foldr : ∀ {α β} -> Γ ⊢ α ⇒ β ⇒ β -> Γ ⊢ β -> Γ ⊢ list ·ᵗ α -> Γ ⊢ β

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
ren ι  []            = []
ren ι (x :: xs)      = ren ι x :: ren ι xs
ren ι (foldr f z xs) = foldr (ren ι f) (ren ι z) (ren ι xs)

shift : ∀ {Θ Γ} {σ τ : Type Θ} -> Γ ⊢ σ -> Γ ▻ τ ⊢ σ
shift = ren top

ren-∘ˢ : ∀ {Θ Γ Δ Ξ} {α : Type Θ} (κ : Δ ⊆ Ξ) (ι : Γ ⊆ Δ) (t : Γ ⊢ α)
       -> ren κ (ren ι t) ≡ ren (κ ∘ˢ ι) t
ren-∘ˢ κ ι (var v)   = cong var (renᵛ-∘ˢ κ ι v)
ren-∘ˢ κ ι (Λ b)     = cong Λ_ (trans (ren-∘ˢ (shiftᶜ-⊆ κ) (shiftᶜ-⊆ ι) b)
                                      (cong (flip ren b) (shiftᶜ-⊆-∘ˢ κ ι)))
ren-∘ˢ κ ι (f [ α ]) = cong _[ α ] (ren-∘ˢ κ ι f)
ren-∘ˢ κ ι (ƛ b)     = cong ƛ_ (ren-∘ˢ (keep κ) (keep ι) b)
ren-∘ˢ κ ι (f · x)   = cong₂ _·_ (ren-∘ˢ κ ι f) (ren-∘ˢ κ ι x)
ren-∘ˢ κ ι  []            = refl
ren-∘ˢ κ ι (x :: xs)      = cong₂ _::_ (ren-∘ˢ κ ι x) (ren-∘ˢ κ ι xs)
ren-∘ˢ κ ι (foldr f z xs) = cong₃ foldr (ren-∘ˢ κ ι f) (ren-∘ˢ κ ι z) (ren-∘ˢ κ ι xs)

TermTh : ∀ {Θ} -> Thing (_⊢_ {Θ})
TermTh = record
  { renᶠ    = ren
  ; renᶠ-∘ˢ = ren-∘ˢ
  }

TermEnv : ∀ {Θ} -> Environment (TermTh {Θ})
TermEnv = record
  { varᶠ      = var
  ; renᶠ-varᶠ = λ ι v -> refl
  }

module TermThing       {Θ} = Thing       (TermTh  {Θ})
module TermEnvironment {Θ} = Environment (TermEnv {Θ})
