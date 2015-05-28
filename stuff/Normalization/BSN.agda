-- stolen from https://github.com/jmchapman/Big-step-Normalisation/tree/master/LambdaCalculus/BasicSystem

{-# OPTIONS --no-termination-check #-}

infixr 5 _⇒_
infixl 6 _▻_
infix  3 _⊢_ _∈_ _⊢ⁿᵉ_ _⊢ⁿᶠ_ _⊢ⁿᵉ[_]_ _⊆_
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

data _⊢ⁿᵉ[_]_ Γ (B : Con -> Type -> Set) : Type -> Set where
  varⁿᵉ : ∀ {σ}   -> σ ∈ Γ            -> Γ ⊢ⁿᵉ[ B ] σ
  _·ⁿᵉ_ : ∀ {σ τ} -> Γ ⊢ⁿᵉ[ B ] σ ⇒ τ -> B Γ σ        -> Γ ⊢ⁿᵉ[ B ] τ

mutual
  data _⊢ⁿᶠ_ Γ : Type -> Set where
    neⁿᶠ : ∀ {σ}   -> Γ ⊢ⁿᵉ σ     -> Γ ⊢ⁿᶠ σ
    ƛⁿᶠ_ : ∀ {σ τ} -> Γ ▻ σ ⊢ⁿᶠ τ -> Γ ⊢ⁿᶠ σ ⇒ τ

  _⊢ⁿᵉ_ : Con -> Type -> Set
  Γ ⊢ⁿᵉ σ = Γ ⊢ⁿᵉ[ _⊢ⁿᶠ_ ] σ

data Env (B : Type -> Set) : Con -> Set where
  ø   : Env B ε
  _▷_ : ∀ {Γ σ} -> Env B Γ -> B σ -> Env B (Γ ▻ σ)

lookup : ∀ {B Γ σ} -> σ ∈ Γ -> Env B Γ -> B σ
lookup  vz    (ρ ▷ y) = y
lookup (vs v) (ρ ▷ y) = lookup v ρ

mutual
  data ⟦_⊢ⁿᶠ_⟧ Δ : Type -> Set where
    neˢᵉᵐ : ∀ {σ}     -> ⟦ Δ ⊢ⁿᵉ σ ⟧ -> ⟦ Δ ⊢ⁿᶠ σ ⟧
    ƛˢᵉᵐ  : ∀ {Γ σ τ} -> Γ ▻ σ ⊢ τ   -> ⟦ Γ ↦ Δ ⟧   -> ⟦ Δ ⊢ⁿᶠ σ ⇒ τ ⟧

  ⟦_⊢ⁿᵉ_⟧ : Con -> Type -> Set
  ⟦ Γ ⊢ⁿᵉ σ ⟧ = Γ ⊢ⁿᵉ[ ⟦_⊢ⁿᶠ_⟧ ] σ

  ⟦_↦_⟧ : Con -> Con -> Set
  ⟦ Γ ↦ Δ ⟧ = Env ⟦ Δ ⊢ⁿᶠ_⟧ Γ

mutual
  ⟦_/_⟧ : ∀ {Γ Δ σ} -> ⟦ Γ ↦ Δ ⟧ -> Γ ⊢ σ -> ⟦ Δ ⊢ⁿᶠ σ ⟧
  ⟦ ρ / var v ⟧ = lookup v ρ
  ⟦ ρ / ƛ b   ⟧ = ƛˢᵉᵐ b ρ
  ⟦ ρ / f · x ⟧ = ⟦ ρ / f ⟧ $ˢᵉᵐ ⟦ ρ / x ⟧

  _$ˢᵉᵐ_ : ∀ {Γ σ τ} -> ⟦ Γ ⊢ⁿᶠ σ ⇒ τ ⟧ -> ⟦ Γ ⊢ⁿᶠ σ ⟧ -> ⟦ Γ ⊢ⁿᶠ τ ⟧
  ƛˢᵉᵐ  b ρ $ˢᵉᵐ x = ⟦ ρ ▷ x / b ⟧
  neˢᵉᵐ f   $ˢᵉᵐ x = neˢᵉᵐ (f ·ⁿᵉ x)

data _⊆_ : Con -> Con -> Set where
  stop : ∀ {Γ}     -> ε ⊆ Γ
  skip : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊆ Δ ▻ σ
  keep : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ▻ σ ⊆ Δ ▻ σ

wkᵛᵃʳ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> σ ∈ Γ -> σ ∈ Δ
wkᵛᵃʳ  stop     ()
wkᵛᵃʳ (skip ψ)  v     = vs (wkᵛᵃʳ ψ v)
wkᵛᵃʳ (keep ψ)  vz    = vz
wkᵛᵃʳ (keep ψ) (vs v) = vs (wkᵛᵃʳ ψ v)

mutual
  wkⁿᵉ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ⁿᵉ σ -> Δ ⊢ⁿᵉ σ
  wkⁿᵉ ψ (varⁿᵉ v) = varⁿᵉ (wkᵛᵃʳ ψ v)
  wkⁿᵉ ψ (f ·ⁿᵉ x) = wkⁿᵉ ψ f ·ⁿᵉ wkⁿᶠ ψ x

  wkⁿᶠ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ⁿᶠ σ -> Δ ⊢ⁿᶠ σ
  wkⁿᶠ ψ (neⁿᶠ n) = neⁿᶠ (wkⁿᵉ ψ n)
  wkⁿᶠ ψ (ƛⁿᶠ  b) = ƛⁿᶠ (wkⁿᶠ (keep ψ) b)

mutual
  wk⟦⟧ⁿᵉ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> ⟦ Γ ⊢ⁿᵉ σ ⟧ -> ⟦ Δ ⊢ⁿᵉ σ ⟧
  wk⟦⟧ⁿᵉ ψ (varⁿᵉ v)   = varⁿᵉ (wkᵛᵃʳ ψ v)
  wk⟦⟧ⁿᵉ ψ (fˢ ·ⁿᵉ xˢ) = wk⟦⟧ⁿᵉ ψ fˢ ·ⁿᵉ wk⟦⟧ⁿᶠ ψ xˢ

  wk⟦⟧ⁿᶠ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> ⟦ Γ ⊢ⁿᶠ σ ⟧ -> ⟦ Δ ⊢ⁿᶠ σ ⟧
  wk⟦⟧ⁿᶠ ψ (neˢᵉᵐ xˢ)  = neˢᵉᵐ (wk⟦⟧ⁿᵉ ψ xˢ)
  wk⟦⟧ⁿᶠ ψ (ƛˢᵉᵐ bˢ ρ) = ƛˢᵉᵐ bˢ (wk⟦⟧ᵉⁿᵛ ψ ρ)

  wk⟦⟧ᵉⁿᵛ : ∀ {Γ Δ Θ} -> Δ ⊆ Θ -> ⟦ Γ ↦ Δ ⟧ -> ⟦ Γ ↦ Θ ⟧
  wk⟦⟧ᵉⁿᵛ ψ  ø       = ø
  wk⟦⟧ᵉⁿᵛ ψ (ρ ▷ xˢ) = wk⟦⟧ᵉⁿᵛ ψ ρ ▷ wk⟦⟧ⁿᶠ ψ xˢ

idˢᵘᵇ : ∀ {Γ} -> Γ ⊆ Γ
idˢᵘᵇ {ε}     = stop
idˢᵘᵇ {ψ ▻ x} = keep idˢᵘᵇ

varˢᵉᵐ : ∀ {Γ σ} -> σ ∈ Γ -> ⟦ Γ ⊢ⁿᶠ σ ⟧
varˢᵉᵐ v = neˢᵉᵐ (varⁿᵉ v)

idᵉⁿᵛ : ∀ {Γ} -> ⟦ Γ ↦ Γ ⟧
idᵉⁿᵛ {ε}     = ø
idᵉⁿᵛ {Γ ▻ σ} = wk⟦⟧ᵉⁿᵛ (skip idˢᵘᵇ) idᵉⁿᵛ ▷ varˢᵉᵐ vz

mutual
  quoteⁿᶠ : ∀ {σ Γ} -> ⟦ Γ ⊢ⁿᶠ σ ⟧ -> Γ ⊢ⁿᶠ σ
  quoteⁿᶠ {ι}     (neˢᵉᵐ x) = neⁿᶠ (quoteⁿᵉ x)
  quoteⁿᶠ {σ ⇒ τ}  f        = ƛⁿᶠ (quoteⁿᶠ (wk⟦⟧ⁿᶠ (skip idˢᵘᵇ) f $ˢᵉᵐ varˢᵉᵐ vz))

  quoteⁿᵉ : ∀ {Γ σ} -> ⟦ Γ ⊢ⁿᵉ σ ⟧ -> Γ ⊢ⁿᵉ σ 
  quoteⁿᵉ (varⁿᵉ v) = varⁿᵉ v
  quoteⁿᵉ (f ·ⁿᵉ x) = quoteⁿᵉ f ·ⁿᵉ quoteⁿᶠ x

mutual
  fromⁿᵉ : ∀ {Γ σ} -> Γ ⊢ⁿᵉ σ -> Γ ⊢ σ
  fromⁿᵉ (varⁿᵉ v) = var v
  fromⁿᵉ (f ·ⁿᵉ x) = fromⁿᵉ f · fromⁿᶠ x

  fromⁿᶠ : ∀ {Γ σ} -> Γ ⊢ⁿᶠ σ -> Γ ⊢ σ
  fromⁿᶠ (neⁿᶠ n) = fromⁿᵉ n
  fromⁿᶠ (ƛⁿᶠ  b) = ƛ (fromⁿᶠ b)

normalize : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢ σ
normalize x = fromⁿᶠ (quoteⁿᶠ ⟦ idᵉⁿᵛ / x ⟧)



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
