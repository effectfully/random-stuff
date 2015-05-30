infixr 5 _⇒_
infixl 6 _▻_
infix  3 _⊢_ _∈_ _⊢ⁿᵉ_ _⊢ⁿᶠ_ _⊆_ _⊢ʷⁿᵉ_ _⊢ʷⁿᶠ_ _↦_
infixr 5 vs_
infixr 4 ƛ_
infixl 6 _·_

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
  stop : ∀ {Γ}     -> Γ ⊆ Γ
  skip : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ     ⊆ Δ ▻ σ
  keep : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ▻ σ ⊆ Δ ▻ σ

topˢᵘᵇ : ∀ {Γ σ} -> Γ ⊆ Γ ▻ σ
topˢᵘᵇ = skip stop

_∘ˢᵘᵇ_ : ∀ {Γ Δ Θ} -> Δ ⊆ Θ -> Γ ⊆ Δ -> Γ ⊆ Θ
stop   ∘ˢᵘᵇ ψ      = ψ
skip φ ∘ˢᵘᵇ ψ      = skip (φ ∘ˢᵘᵇ ψ)
keep φ ∘ˢᵘᵇ stop   = keep φ
keep φ ∘ˢᵘᵇ skip ψ = skip (φ ∘ˢᵘᵇ ψ)
keep φ ∘ˢᵘᵇ keep ψ = keep (φ ∘ˢᵘᵇ ψ)

mutual
  data _⊢ʷⁿᵉ_ Δ : Type -> Set where
    varʷⁿᵉ    : ∀ {σ}   -> σ ∈ Δ        -> Δ ⊢ʷⁿᵉ σ
    _·ʷⁿᵉ_    : ∀ {σ τ} -> Δ ⊢ʷⁿᵉ σ ⇒ τ -> Δ ⊢ʷⁿᶠ σ -> Δ ⊢ʷⁿᵉ τ
    weakenʷⁿᵉ : ∀ {Γ σ} -> Γ ⊆ Δ        -> Γ ⊢ʷⁿᵉ σ -> Δ ⊢ʷⁿᵉ σ

  data _⊢ʷⁿᶠ_ Γ : Type -> Set where
    neʷ   : ∀ {σ}   -> Γ ⊢ʷⁿᵉ σ     -> Γ ⊢ʷⁿᶠ σ
    ƛʷⁿᶠ_ : ∀ {σ τ} -> Γ ▻ σ ⊢ʷⁿᶠ τ -> Γ ⊢ʷⁿᶠ σ ⇒ τ

⟦_⟧ᵀ : Type -> Con -> Set
⟦ ι     ⟧ᵀ Γ = Γ ⊢ʷⁿᵉ ι
⟦ σ ⇒ τ ⟧ᵀ Γ = ∀ {Δ} -> Γ ⊆ Δ -> ⟦ σ ⟧ᵀ Δ -> ⟦ τ ⟧ᵀ Δ

mutual
  ↑ : ∀ {σ Γ} -> Γ ⊢ʷⁿᵉ σ -> ⟦ σ ⟧ᵀ Γ
  ↑ {ι}     x = x
  ↑ {σ ⇒ τ} f = λ ψ y -> ↑ (weakenʷⁿᵉ ψ f ·ʷⁿᵉ ↓ y)

  ↓ : ∀ {σ Γ} -> ⟦ σ ⟧ᵀ Γ -> Γ ⊢ʷⁿᶠ σ
  ↓ {ι}     x = neʷ x
  ↓ {σ ⇒ τ} f = ƛʷⁿᶠ (↓ (f topˢᵘᵇ (varˢᵉᵐ vz)))

  varˢᵉᵐ : ∀ {Γ σ} -> σ ∈ Γ -> ⟦ σ ⟧ᵀ Γ
  varˢᵉᵐ v = ↑ (varʷⁿᵉ v)

weakenᵛᵃʳ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> σ ∈ Γ -> σ ∈ Δ
weakenᵛᵃʳ  stop     v     = v
weakenᵛᵃʳ (skip ψ)  v     = vs (weakenᵛᵃʳ ψ v)
weakenᵛᵃʳ (keep ψ)  vz    = vz
weakenᵛᵃʳ (keep ψ) (vs v) = vs (weakenᵛᵃʳ ψ v)

mutual
  unʷⁿᵉ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ʷⁿᵉ σ -> Δ ⊢ⁿᵉ σ
  unʷⁿᵉ φ (varʷⁿᵉ v)      = varⁿᵉ (weakenᵛᵃʳ φ v)
  unʷⁿᵉ φ (f ·ʷⁿᵉ x)      = unʷⁿᵉ φ f ·ⁿᵉ unʷⁿᶠ φ x
  unʷⁿᵉ φ (weakenʷⁿᵉ ψ x) = unʷⁿᵉ (φ ∘ˢᵘᵇ ψ) x

  unʷⁿᶠ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ʷⁿᶠ σ -> Δ ⊢ⁿᶠ σ
  unʷⁿᶠ ψ (neʷ x)  = ne (unʷⁿᵉ ψ x)
  unʷⁿᶠ ψ (ƛʷⁿᶠ b) = ƛⁿᶠ (unʷⁿᶠ (keep ψ) b)

data _↦_ : Con -> Con -> Set where
  Ø         : ∀ {Γ}     -> ε ↦ Γ
  _▷_       : ∀ {Γ Δ σ} -> Γ ↦ Δ -> ⟦ σ ⟧ᵀ Δ -> Γ ▻ σ ↦ Δ
  weakenᵉⁿᵛ : ∀ {Γ Δ Θ} -> Δ ⊆ Θ -> Γ ↦ Δ    -> Γ ↦ Θ

weakenˢᵉᵐ : ∀ {σ Γ Δ} -> Γ ⊆ Δ -> ⟦ σ ⟧ᵀ Γ -> ⟦ σ ⟧ᵀ Δ
weakenˢᵉᵐ {ι}     ψ x = weakenʷⁿᵉ ψ x
weakenˢᵉᵐ {σ ⇒ τ} ψ f = λ φ y -> f (φ ∘ˢᵘᵇ ψ) y

lookupᵉⁿᵛ : ∀ {Γ Δ Θ σ} -> Δ ⊆ Θ -> σ ∈ Γ -> Γ ↦ Δ -> ⟦ σ ⟧ᵀ Θ
lookupᵉⁿᵛ φ  vz    (ρ ▷ y)         = weakenˢᵉᵐ φ y
lookupᵉⁿᵛ φ (vs v) (ρ ▷ y)         = lookupᵉⁿᵛ φ v ρ
lookupᵉⁿᵛ φ  v     (weakenᵉⁿᵛ ψ ρ) = lookupᵉⁿᵛ (φ ∘ˢᵘᵇ ψ) v ρ

⟦_⟧ : ∀ {Γ Δ σ} -> Γ ⊢ σ -> Γ ↦ Δ -> ⟦ σ ⟧ᵀ Δ
⟦ var v ⟧ ρ = lookupᵉⁿᵛ stop v ρ
⟦ ƛ b   ⟧ ρ = λ ψ y -> ⟦ b ⟧ (weakenᵉⁿᵛ ψ ρ ▷ y)
⟦ f · x ⟧ ρ = ⟦ f ⟧ ρ stop (⟦ x ⟧ ρ)

idᵉⁿᵛ : ∀ {Γ} -> Γ ↦ Γ
idᵉⁿᵛ {ε}     = Ø
idᵉⁿᵛ {Γ ▻ σ} = weakenᵉⁿᵛ topˢᵘᵇ idᵉⁿᵛ ▷ varˢᵉᵐ vz

norm : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢ σ
norm x = fromⁿᶠ (unʷⁿᶠ stop (↓ (⟦ x ⟧ idᵉⁿᵛ)))



open import Relation.Binary.PropositionalEquality

Term : Type -> Set
Term σ = ε ⊢ σ

I : Term (ι ⇒ ι)
I = ƛ var vz

K : Term (ι ⇒ ι ⇒ ι)
K = ƛ ƛ var (vs vz)

S : Term ((ι ⇒ ι ⇒ ι) ⇒ (ι ⇒ ι) ⇒ ι ⇒ ι)
S = ƛ ƛ ƛ var (vs vs vz) · var vz · (var (vs vz) · var vz)

test : norm (S · K · I) ≡ I
test = refl
