module TT.Core where

open import TT.Prelude public

infixr 3 ƛ_
infixl 6 _·_
infix  2 _::_

mutual
  Type = Term

  data Term n : Set where
    type : Type n
    π    : Type n -> Type (suc n) -> Type n
    var  : Fin n -> Term n
    ƛ_   : Term (suc n) -> Term n
    _·_  : Term n -> Term n -> Term n
    _::_ : Term n -> Type n -> Term n

Term⁽⁾ = Term 0
Term⁺  = ∀ {n} -> Term n

erase : ∀ {n} -> Term n -> Term n
erase  type    = type
erase (π σ τ)  = π (erase σ) (erase τ)
erase (var v)  = var v
erase (ƛ b)    = ƛ (erase b)
erase (f · x)  = erase f · erase x
erase (x :: σ) = erase x

instance
  Term-MEq : ∀ {n} -> MEq (Term n)
  Term-MEq = record { _≟_ = eq } where
    eq : ∀ {n} -> (t₁ t₂ : Term n) -> Maybe (t₁ ≡ t₂)
    eq  type       type      = just refl
    eq (π σ₁ τ₁)  (π σ₂ τ₂)  = cong₂ π    <$> eq σ₁ σ₂ ⊛ eq τ₁ τ₂ 
    eq (var v₁)   (var v₂)   = cong  var  <$> v₁ ≟ v₂
    eq (ƛ b₁)     (ƛ b₂)     = cong  ƛ_   <$> eq b₁ b₂
    eq (f₁ · x₁)  (f₂ · x₂)  = cong₂ _·_  <$> eq f₁ f₂ ⊛ eq x₁ x₂
    eq (x₁ :: σ₁) (x₂ :: σ₂) = cong₂ _::_ <$> eq x₁ x₂ ⊛ eq σ₁ σ₂
    eq  _         _          = nothing

data _≤_ : ℕ -> ℕ -> Set where
  stop : ∀ {n}   -> n ≤ n
  skip : ∀ {n m} -> n ≤ m -> n     ≤ suc m
  keep : ∀ {n m} -> n ≤ m -> suc n ≤ suc m

top : ∀ {n} -> n ≤ suc n
top = skip stop

full : ∀ {n} -> 0 ≤ n
full {0}     = stop
full {suc n} = skip full

_∘ˡᵉ_ : ∀ {n m p} -> m ≤ p -> n ≤ m -> n ≤ p
stop   ∘ˡᵉ ι      = ι
skip κ ∘ˡᵉ ι      = skip (κ ∘ˡᵉ ι)
keep κ ∘ˡᵉ stop   = keep κ
keep κ ∘ˡᵉ skip ι = skip (κ ∘ˡᵉ ι)
keep κ ∘ˡᵉ keep ι = keep (κ ∘ˡᵉ ι)

renᶠ : ∀ {n m} -> n ≤ m -> Fin n -> Fin m
renᶠ  stop     v      = v
renᶠ (skip ι)  v      = suc (renᶠ ι v)
renᶠ (keep ι)  zero   = zero
renᶠ (keep ι) (suc v) = suc (renᶠ ι v)

ren : ∀ {n m} -> n ≤ m -> Term n -> Term m
ren ι  type    = type
ren ι (π σ τ)  = π (ren ι σ) (ren (keep ι) τ)
ren ι (var v)  = var (renᶠ ι v)
ren ι (ƛ b)    = ƛ (ren (keep ι) b)
ren ι (f · x)  = ren ι f · ren ι x
ren ι (x :: σ) = ren ι x :: ren ι σ

record IsThing : Set₁ where
  infixl 6 _·ᵏ_
  infixr 9 _∘ᵏ_

  field Thing : ℕ -> Set

  Kripke : ℕ -> Set
  Kripke n = ∀ {m} -> n ≤ m -> Thing m -> Thing m

  renᵏ : ∀ {n m} -> n ≤ m -> Kripke n -> Kripke m
  renᵏ ι k κ = k (κ ∘ˡᵉ ι)

  _·ᵏ_ : ∀ {n} -> Kripke n -> Thing n -> Thing n
  k ·ᵏ t = k stop t

  _∘ᵏ_ : ∀ {n} -> Kripke n -> Kripke n -> Kripke n
  (k₂ ∘ᵏ k₁) ι = k₂ ι ∘ k₁ ι

record Context (isThing : IsThing) : Set where
  infixl 5 _▻_

  open IsThing isThing

  field renᵗ : ∀ {n m} -> n ≤ m -> Thing n -> Thing m

  shift : ∀ {n} -> Thing n -> Thing (suc n)
  shift = renᵗ top

  data Con : ℕ -> Set where
    ε   : Con 0
    _▻_ : ∀ {n} -> Con n -> Thing n -> Con (suc n)

  lookupᶜ : ∀ {n} -> Fin n -> Con n -> Thing n
  lookupᶜ  zero   (Γ ▻ t) = shift t
  lookupᶜ (suc v) (Γ ▻ t) = shift (lookupᶜ v Γ)

record Environment {isThing} (context : Context isThing) : Set where
  infixl 5 _▷_

  open IsThing isThing
  open Context context

  field fresh : ∀ {n} -> Thing (suc n)

  apᵏ : ∀ {n} -> Kripke n -> Thing (suc n)
  apᵏ k = k top fresh

  data Env n : ℕ -> Set where
    ø   : Env n 0
    _▷_ : ∀ {m} -> Env n m -> Thing n -> Env n (suc m)

  lookupᵉ : ∀ {n m} -> Fin m -> Env n m -> Thing n
  lookupᵉ  zero   (ψ ▷ t) = t
  lookupᵉ (suc v) (ψ ▷ t) = lookupᵉ v ψ

  renᵉ : ∀ {n m l} -> n ≤ m -> Env n l -> Env m l
  renᵉ ι  ø      = ø
  renᵉ ι (ψ ▷ t) = renᵉ ι ψ ▷ renᵗ ι t

  skipᵉ : ∀ {n m} -> Env n m -> Env (suc n) m
  skipᵉ = renᵉ top

  keepᵉ : ∀ {n m} -> Env n m -> Env (suc n) (suc m)
  keepᵉ ψ = skipᵉ ψ ▷ fresh

  stopᵉ : ∀ {n} -> Env n n
  stopᵉ {0}     = ø
  stopᵉ {suc n} = keepᵉ stopᵉ

TermIsThing : IsThing
TermIsThing = record { Thing = Term }

TermCon : Context TermIsThing
TermCon = record { renᵗ = ren }

TermEnv : Environment TermCon
TermEnv = record { fresh = var zero }

module TermContext     = Context     TermCon
module TermEnvironment = Environment TermEnv
