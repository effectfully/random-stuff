infixr 5 _⇒_
infixl 6 _▻_
infix  3 _⊢_ _∈_ _⊢ⁿᵉ_ _⊢ⁿᶠ_ _⊆_
infixr 3 vs_
infixr 2 ƛ_
infixl 5 _·_

data Type : Set where
  ι    : Type
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
  _·_ : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ

mutual
  data _⊢ⁿᵉ_ Γ : Type -> Set where
    varⁿᵉ : ∀ {σ}   -> σ ∈ Γ       -> Γ ⊢ⁿᵉ σ
    _·ⁿᵉ_ : ∀ {σ τ} -> Γ ⊢ⁿᵉ σ ⇒ τ -> Γ ⊢ⁿᶠ σ -> Γ ⊢ⁿᵉ τ

  data _⊢ⁿᶠ_ Γ : Type -> Set where
    ne   : ∀ {σ}   -> Γ ⊢ⁿᵉ σ     -> Γ ⊢ⁿᶠ σ
    ƛⁿᶠ_ : ∀ {σ τ} -> Γ ▻ σ ⊢ⁿᶠ τ -> Γ ⊢ⁿᶠ σ ⇒ τ

mutual
  fromⁿᵉ : ∀ {Γ σ} -> Γ ⊢ⁿᵉ σ -> Γ ⊢ σ
  fromⁿᵉ (varⁿᵉ v) = var v
  fromⁿᵉ (f ·ⁿᵉ x) = fromⁿᵉ f · fromⁿᶠ x

  fromⁿᶠ : ∀ {Γ σ} -> Γ ⊢ⁿᶠ σ -> Γ ⊢ σ
  fromⁿᶠ (ne n)  = fromⁿᵉ n
  fromⁿᶠ (ƛⁿᶠ b) = ƛ (fromⁿᶠ b)

data _⊆_ : Con -> Con -> Set where
  stop : ε ⊆ ε
  skip : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ     ⊆ Δ ▻ σ
  keep : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ▻ σ ⊆ Δ ▻ σ

idˢᵘᵇ : ∀ {Γ} -> Γ ⊆ Γ
idˢᵘᵇ {ε}     = stop
idˢᵘᵇ {Γ ▻ σ} = keep idˢᵘᵇ

topˢᵘᵇ : ∀ {Γ σ} -> Γ ⊆ Γ ▻ σ
topˢᵘᵇ = skip idˢᵘᵇ

_∘ˢᵘᵇ_ : ∀ {Γ Δ Θ} -> Δ ⊆ Θ -> Γ ⊆ Δ -> Γ ⊆ Θ
stop   ∘ˢᵘᵇ ψ      = ψ
skip φ ∘ˢᵘᵇ ψ      = skip (φ ∘ˢᵘᵇ ψ)
keep φ ∘ˢᵘᵇ skip ψ = skip (φ ∘ˢᵘᵇ ψ)
keep φ ∘ˢᵘᵇ keep ψ = keep (φ ∘ˢᵘᵇ ψ)

weakenᵛᵃʳ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> σ ∈ Γ -> σ ∈ Δ
weakenᵛᵃʳ  stop     ()
weakenᵛᵃʳ (skip ψ)  v     = vs (weakenᵛᵃʳ ψ v)
weakenᵛᵃʳ (keep ψ)  vz    = vz
weakenᵛᵃʳ (keep ψ) (vs v) = vs (weakenᵛᵃʳ ψ v)

mutual
  weakenⁿᵉ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ⁿᵉ σ -> Δ ⊢ⁿᵉ σ
  weakenⁿᵉ ψ (varⁿᵉ v) = varⁿᵉ (weakenᵛᵃʳ ψ v)
  weakenⁿᵉ ψ (f ·ⁿᵉ x) = weakenⁿᵉ ψ f ·ⁿᵉ weakenⁿᶠ ψ x

  weakenⁿᶠ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ⁿᶠ σ -> Δ ⊢ⁿᶠ σ
  weakenⁿᶠ ψ (ne n)  = ne (weakenⁿᵉ ψ n)
  weakenⁿᶠ ψ (ƛⁿᶠ b) = ƛⁿᶠ (weakenⁿᶠ (keep ψ) b)

⟦_⟧ᵀ : Type -> Con -> Set
⟦ ι     ⟧ᵀ Γ = Γ ⊢ⁿᵉ ι
⟦ σ ⇒ τ ⟧ᵀ Γ = ∀ {Δ} -> Γ ⊆ Δ -> ⟦ σ ⟧ᵀ Δ -> ⟦ τ ⟧ᵀ Δ

weakenˢᵉᵐ : ∀ {σ Γ Δ} -> Γ ⊆ Δ -> ⟦ σ ⟧ᵀ Γ -> ⟦ σ ⟧ᵀ Δ
weakenˢᵉᵐ {ι}     ψ x = weakenⁿᵉ ψ x
weakenˢᵉᵐ {σ ⇒ τ} ψ f = λ φ y -> f (φ ∘ˢᵘᵇ ψ) y

mutual
  ↑ : ∀ {σ Γ} -> Γ ⊢ⁿᵉ σ -> ⟦ σ ⟧ᵀ Γ
  ↑ {ι}     n = n
  ↑ {σ ⇒ τ} f = λ ψ y -> ↑ (weakenⁿᵉ ψ f ·ⁿᵉ ↓ y)

  ↓ : ∀ {σ Γ} -> ⟦ σ ⟧ᵀ Γ -> Γ ⊢ⁿᶠ σ
  ↓ {ι}     n = ne n
  ↓ {σ ⇒ τ} f = ƛⁿᶠ (↓ (f topˢᵘᵇ (varˢᵉᵐ vz)))

  varˢᵉᵐ : ∀ {Γ σ} -> σ ∈ Γ -> ⟦ σ ⟧ᵀ Γ
  varˢᵉᵐ v = ↑ (varⁿᵉ v)

data Env (B : Type -> Set) : Con -> Set where
  Ø    : Env B ε
  _▷_ : ∀ {Γ σ} -> Env B Γ -> B σ -> Env B (Γ ▻ σ)

lookupᵉⁿᵛ : ∀ {B Γ σ} -> σ ∈ Γ -> Env B Γ -> B σ
lookupᵉⁿᵛ  vz    (ρ ▷ y) = y
lookupᵉⁿᵛ (vs v) (ρ ▷ y) = lookupᵉⁿᵛ v ρ

mapᵉⁿᵛ : ∀ {B C : Type -> Set} {Γ}
        -> (∀ {σ} -> B σ -> C σ) -> Env B Γ -> Env C Γ
mapᵉⁿᵛ f  Ø      = Ø
mapᵉⁿᵛ f (ρ ▷ y) = mapᵉⁿᵛ f ρ ▷ f y

_↦_ : Con -> Con -> Set
Γ ↦ Δ = Env (λ σ -> ⟦ σ ⟧ᵀ Δ) Γ

idᵉⁿᵛ : ∀ {Γ} -> Γ ↦ Γ
idᵉⁿᵛ {ε}     = Ø
idᵉⁿᵛ {Γ ▻ σ} = mapᵉⁿᵛ (weakenˢᵉᵐ topˢᵘᵇ) idᵉⁿᵛ ▷ varˢᵉᵐ vz

⟦_⟧ : ∀ {Γ Δ σ} -> Γ ⊢ σ -> Γ ↦ Δ -> ⟦ σ ⟧ᵀ Δ
⟦ var v ⟧ ρ = lookupᵉⁿᵛ v ρ
⟦ ƛ b   ⟧ ρ = λ φ y -> ⟦ b ⟧ (mapᵉⁿᵛ (weakenˢᵉᵐ φ) ρ ▷ y)
⟦ f · x ⟧ ρ = ⟦ f ⟧ ρ idˢᵘᵇ (⟦ x ⟧ ρ)

normalize : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢ σ
normalize x = fromⁿᶠ (↓ (⟦ x ⟧ idᵉⁿᵛ))



open import Relation.Binary.PropositionalEquality

Term : Type -> Set
Term σ = ε ⊢ σ

I : Term (ι ⇒ ι)
I = ƛ var vz

K : Term (ι ⇒ ι ⇒ ι)
K = ƛ ƛ var (vs vz)

S : Term ((ι ⇒ ι ⇒ ι) ⇒ (ι ⇒ ι) ⇒ ι ⇒ ι)
S = ƛ ƛ ƛ var (vs vs vz) · var vz · (var (vs vz) · var vz)

test : normalize (S · K · I) ≡ I
test = refl
