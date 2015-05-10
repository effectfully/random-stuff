-- stolen from http://www.cse.chalmers.se/~nad/listings/simply-typed/

open import Relation.Binary.PropositionalEquality hiding ([_])

infixr 2 _⇒_
infixr 5 _▻_ _▻▻_
infix  1 _∋_ _⊢_ _⊢ⁿᵉ_ _⊢ⁿᶠ_ _⊆_
infixr 2 ƛ_
infixl 4 _·_

data Type : Set where
  ι    : Type
  _⇒_ : Type -> Type -> Type

data Con : Set where
  ε   : Con
  _▻_ : Con -> Type -> Con

_▻▻_ : Con -> Con -> Con
Γ ▻▻  ε      = Γ
Γ ▻▻ (Δ ▻ σ) = (Γ ▻▻ Δ) ▻ σ

▻▻-assoc : ∀ {Γ Δ} Ε -> Γ ▻▻ (Δ ▻▻ Ε) ≡ (Γ ▻▻ Δ) ▻▻ Ε
▻▻-assoc  ε      = refl
▻▻-assoc (Ε ▻ σ) = cong (λ Γ -> Γ ▻ σ) (▻▻-assoc Ε)

data _∋_ : Con -> Type -> Set where
  vz  : ∀ {Γ σ}   -> Γ ▻ σ ∋ σ
  vs_ : ∀ {Γ σ τ} -> Γ     ∋ σ -> Γ ▻ τ ∋ σ

_⊆_ : Con -> Con -> Set
Γ ⊆ Δ = ∀ {σ} -> Γ ∋ σ -> Δ ∋ σ

weakenˢᵘᵇ : ∀ {Γ} Δ -> Γ ⊆ Γ ▻▻ Δ
weakenˢᵘᵇ  ε      v = v
weakenˢᵘᵇ (Δ ▻ σ) v = vs (weakenˢᵘᵇ Δ v)

keep : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ▻ σ ⊆ Δ ▻ σ
keep sub  vz    = vz
keep sub (vs v) = vs (sub v)

data _⊢_ Γ : Type -> Set where
  var : ∀ {σ}   -> Γ ∋ σ     -> Γ ⊢ σ
  ƛ_  : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _·_ : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ

mutual
  data _⊢ⁿᵉ_ Γ : Type -> Set where
    varⁿᵉ : ∀ {σ}   -> Γ ∋ σ      -> Γ ⊢ⁿᵉ σ
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

mutual
  weakenⁿᵉ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ⁿᵉ σ -> Δ ⊢ⁿᵉ σ
  weakenⁿᵉ sub (varⁿᵉ v) = varⁿᵉ (sub v)
  weakenⁿᵉ sub (f ·ⁿᵉ x) = weakenⁿᵉ sub f ·ⁿᵉ weakenⁿᶠ sub x

  weakenⁿᶠ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ⁿᶠ σ -> Δ ⊢ⁿᶠ σ
  weakenⁿᶠ sub (ne n)  = ne (weakenⁿᵉ sub n)
  weakenⁿᶠ sub (ƛⁿᶠ b) = ƛⁿᶠ (weakenⁿᶠ (keep sub) b)

[_/_] : Con -> Type -> Set
[ Γ / ι     ] = Γ ⊢ⁿᵉ ι
[ Γ / σ ⇒ τ ] = ∀ Δ -> [ Γ ▻▻ Δ / σ ] -> [ Γ ▻▻ Δ / τ ]

cast : ∀ {Γ Δ σ} -> Γ ≡ Δ -> [ Γ / σ ] -> [ Δ / σ ]
cast refl y = y

weakenˢᵉᵐ : ∀ {σ Γ} Δ -> [ Γ / σ ] -> [ Γ ▻▻ Δ / σ ]
weakenˢᵉᵐ {ι}     Δ n = weakenⁿᵉ (weakenˢᵘᵇ Δ) n
weakenˢᵉᵐ {σ ⇒ τ} Δ f = λ Ε y ->
  cast (▻▻-assoc Ε) (f (Δ ▻▻ Ε) (cast (sym (▻▻-assoc Ε)) y))

mutual
  ↑ : ∀ {σ Γ} -> Γ ⊢ⁿᵉ σ -> [ Γ / σ ]
  ↑ {ι}     n = n
  ↑ {σ ⇒ τ} f = λ Δ y -> ↑ (weakenⁿᵉ (weakenˢᵘᵇ Δ) f ·ⁿᵉ ↓ y)

  ↓ : ∀ {σ Γ} -> [ Γ / σ ] -> Γ ⊢ⁿᶠ σ
  ↓ {ι}     n = ne n
  ↓ {σ ⇒ τ} f = ƛⁿᶠ (↓ (f (ε ▻ σ) (↑ (varⁿᵉ vz))))

data Env (B : Type -> Set) : Con -> Set where
  Ø    : Env B ε
  _▷_ : ∀ {Γ σ} -> Env B Γ -> B σ -> Env B (Γ ▻ σ)

lookup : ∀ {B Γ σ} -> Γ ∋ σ -> Env B Γ -> B σ
lookup  vz    (ρ ▷ y) = y
lookup (vs v) (ρ ▷ y) = lookup v ρ

map-Env : ∀ {B C : Type -> Set} {Γ}
        -> (∀ {σ} -> B σ -> C σ) -> Env B Γ -> Env C Γ
map-Env f  Ø       = Ø
map-Env f (ρ ▷ y) = map-Env f ρ ▷ f y

_=>_ : Con -> Con -> Set
Γ => Δ = Env (λ σ -> [ Δ / σ ]) Γ

varˢᵉᵐ : ∀ {Γ σ} -> Γ ∋ σ -> [ Γ / σ ]
varˢᵉᵐ v = ↑ (varⁿᵉ v)

idˢᵘᵇ : ∀ {Γ} -> Γ => Γ
idˢᵘᵇ {ε}     = Ø
idˢᵘᵇ {Γ ▻ σ} = map-Env (weakenˢᵉᵐ (ε ▻ σ)) idˢᵘᵇ ▷ varˢᵉᵐ vz

[_] : ∀ {Γ Δ σ} -> Γ ⊢ σ -> Γ => Δ -> [ Δ / σ ]
[ var v ] ρ = lookup v ρ
[ ƛ b   ] ρ = λ Ε y -> [ b ] (map-Env (weakenˢᵉᵐ Ε) ρ ▷ y)
[ f · x ] ρ = [ f ] ρ ε ([ x ] ρ)

normalize : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢ σ
normalize e = fromⁿᶠ (↓ ([ e ] idˢᵘᵇ))


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
