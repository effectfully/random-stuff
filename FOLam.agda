{-# OPTIONS --no-positivity-check --no-termination-check #-}

open import Level using (_⊔_)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Unit.Base using (⊤; tt)
open import Data.Nat.Base  hiding (_≟_; _⊔_)
open import Data.Fin renaming (zero to fzero; suc to fsuc) using (Fin)
import Data.Fin.Properties as FinProp
open import Data.Maybe as Maybe
open import Category.Monad

open RawMonad {{...}}

infix  4 _⊑_
infixl 6 _·_
infixl 5 _▻_
infixl 8 _[_]ᵏ

_∸>_ : ∀ {ι α β} {I : Set ι} -> (I -> Set α) -> (I -> Set β) -> Set (ι ⊔ α ⊔ β)
A ∸> B = ∀ {i} -> A i -> B i

Fam : ∀ {α β γ} {A : Set α} {B : A -> Set β}
    -> (∀ {x} -> B x -> Set γ) -> (∀ x -> B x) -> Set (α ⊔ γ)
Fam F f = ∀ {x} -> F (f x)

instance
  maybeMonad : ∀ {α} -> RawMonad {α} Maybe
  maybeMonad = Maybe.monad

MEquates : ∀ {α} -> Set α -> Set α
MEquates A = (x y : A) -> Maybe (x ≡ y)

record MEq {α} (A : Set α) : Set α where
  infix 7 _≟_
  field _≟_ : MEquates A
open MEq {{...}} public

instance
  finMEq : Fam MEq Fin
  finMEq = record { _≟_ = λ i j -> decToMaybe (i FinProp.≟ j) }

cong₃ : ∀ {α β γ δ} {A : Set α} {B : Set β} {C : Set γ} {D : Set δ} {x₁ x₂ y₁ y₂ z₁ z₂}
      -> (f : A -> B -> C -> D) -> x₁ ≡ x₂ -> y₁ ≡ y₂ -> z₁ ≡ z₂ -> f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
cong₃ f refl refl refl = refl

data _⊑_ : ℕ -> ℕ -> Set where
  stop : ∀ {n}   -> n ⊑ n
  skip : ∀ {n m} -> n ⊑ m -> n     ⊑ suc m
  keep : ∀ {n m} -> n ⊑ m -> suc n ⊑ suc m

Weakens : (ℕ -> Set) -> Set
Weakens Fam = ∀ {n m} -> Fam n -> Fam (n + m)

Renames : (ℕ -> Set) -> Set
Renames Fam = ∀ {n m} -> n ⊑ m -> Fam n -> Fam m

top : ∀ {n} -> n ⊑ suc n
top = skip stop

full : ∀ {n} -> 0 ⊑ n
full {0}     = stop
full {suc n} = skip full

keep+ : ∀ {n m} -> n ⊑ n + m
keep+ {0}     = full
keep+ {suc n} = keep keep+

_∘ˢ_ : ∀ {n m p} -> m ⊑ p -> n ⊑ m -> n ⊑ p
stop   ∘ˢ ι      = ι
skip κ ∘ˢ ι      = skip (κ ∘ˢ ι)
keep κ ∘ˢ stop   = keep  κ
keep κ ∘ˢ skip ι = skip (κ ∘ˢ ι)
keep κ ∘ˢ keep ι = keep (κ ∘ˢ ι)

renᶠ : Renames Fin
renᶠ  stop     v       = v
renᶠ (skip ι)  v       = fsuc (renᶠ ι v)
renᶠ (keep ι)  fzero   = fzero
renᶠ (keep ι) (fsuc v) = fsuc (renᶠ ι v)

----------

data Binder : Set where
  πᵇ ƛᵇ : Binder

mutual
  Type = Term

  data Term n : Set where
    type : Type n
    bind : Binder -> Type n -> Term (suc n) -> Type n
    var  : Fin  n -> Term n
    _·_  : Term n -> Term n -> Term  n

pattern π σ τ = bind πᵇ σ τ
pattern ƛ σ t = bind ƛᵇ σ t

Term⁽⁾ : Set
Term⁽⁾ = Term 0

Term⁺ : Set
Term⁺ = ∀ {n} -> Term n
  
Type⁽⁾ = Term⁽⁾
Type⁺  = Term⁺

data Con : ℕ -> Set where
  ε   : Con 0
  _▻_ : ∀ {n} -> Con n -> Term n -> Con (suc n)

ren : Renames Term
ren ι  type        = type
ren ι (bind b σ t) = bind b (ren ι σ) (ren (keep ι) t)
ren ι (var v)      = var (renᶠ ι v)
ren ι (f · x)      = ren ι f · ren ι x

shift : ∀ {n} -> Term n -> Term (suc n)
shift = ren top

lookupᶜ : ∀ {n} -> Fin n -> Con n -> Term n
lookupᶜ  fzero   (Γ ▻ t) = shift t
lookupᶜ (fsuc v) (Γ ▻ t) = shift (lookupᶜ v Γ)

instance
  binderMEq : MEq Binder
  binderMEq = record { _≟_ = go } where
    go : MEquates Binder
    go πᵇ πᵇ = just refl
    go ƛᵇ ƛᵇ = just refl
    go _  _  = nothing

  termMEq : Fam MEq Term
  termMEq = record { _≟_ = go } where
    go : Fam MEquates Term
    go  type            type           = just refl
    go (bind b₁ σ₁ t₁) (bind b₂ σ₂ t₂) = cong₃ bind <$> b₁ ≟ b₂  ⊛ go σ₁ σ₂ ⊛ go t₁ t₂ 
    go (var v₁)        (var v₂)        = cong  var  <$> v₁ ≟ v₂
    go (f₁ · x₁)       (f₂ · x₂)       = cong₂ _·_  <$> go f₁ f₂ ⊛ go x₁ x₂
    go  _               _              = nothing

----------

mutual
  data Value n : Set where
    typeᵛ : Value n
    suspᵛ : ∀ {l} -> Con l -> n ↤ l -> Type l -> Term (suc l) -> Value n
    varᵛ  : Fin   n -> Value  n
    piᵛ   : Value n -> Kripke n -> Value n
    _·ᵛ_  : Value n -> Value  n -> Value n

  data _↤_ m : ℕ -> Set where
    ø   : m ↤ 0
    _▷_ : ∀ {n} -> m ↤ n -> Value m -> m ↤ suc n

  Kripke : ℕ -> Set
  Kripke n = ∀ {m} -> n ⊑ m -> Value m -> Value m

Value⁽⁾ : Set
Value⁽⁾ = Value 0

fresh : ∀ {n} -> Value (suc n)
fresh = varᵛ fzero

_[_]ᵏ : ∀ {n} -> Kripke n -> Value n -> Value n
k [ t ]ᵏ = k stop t

renᵏ : Renames Kripke
renᵏ ι k κ = k (κ ∘ˢ ι)

wkᵏ : Weakens Kripke
wkᵏ = renᵏ keep+

_∘ᵏ_ : ∀ {n} -> Kripke n -> Kripke n -> Kripke n
(k₂ ∘ᵏ k₁) ι = k₂ ι ∘ k₁ ι

instᵏ : ∀ {n} -> Kripke n -> Value (suc n)
instᵏ k = k top fresh

lookupᵉ : ∀ {n m} -> Fin n -> m ↤ n -> Value m
lookupᵉ  fzero   (ψ ▷ x) = x
lookupᵉ (fsuc v) (ψ ▷ x) = lookupᵉ v ψ

mutual
  renᵛ : Renames Value
  renᵛ ι  typeᵛ          = typeᵛ
  renᵛ ι (piᵛ σ τₖ)      = piᵛ (renᵛ ι σ) (renᵏ ι τₖ)
  renᵛ ι (varᵛ v)        = varᵛ (renᶠ ι v)
  renᵛ ι (suspᵛ Γ ψ σ b) = suspᵛ Γ (renᵉ ι ψ) σ b
  renᵛ ι (f ·ᵛ x)        = renᵛ ι f ·ᵛ renᵛ ι x

  renᵉ : ∀ {n} -> Renames (_↤ n)
  renᵉ ι  ø      = ø
  renᵉ ι (ψ ▷ x) = renᵉ ι ψ ▷ renᵛ ι x

skipᵉ : ∀ {n m} -> m ↤ n -> suc m ↤ n
skipᵉ = renᵉ top

keepᵉ : ∀ {n m} -> m ↤ n -> suc m ↤ suc n
keepᵉ ψ = skipᵉ ψ ▷ fresh

----------

mutual
  eval : ∀ {n m} -> Con n -> m ↤ n -> Term n -> Value m
  eval Γ ψ  type   = typeᵛ
  eval Γ ψ (π σ τ) = piᵛ (eval Γ ψ σ) (evalᵏ (Γ ▻ σ) ψ τ)
  eval Γ ψ (var v) = lookupᵉ v ψ
  eval Γ ψ (ƛ σ b) = suspᵛ Γ ψ σ b
  eval Γ ψ (f · x) = eval Γ ψ f ·ᵛ eval Γ ψ x

  evalᵏ : ∀ {n m} -> Con (suc n) -> m ↤ n -> Term (suc n) -> Kripke m
  evalᵏ Γ ψ t ι x = eval Γ (renᵉ ι ψ ▷ x) t

  _$ᵛ_ : ∀ {n} -> Value n -> Value n -> Value n
  suspᵛ Γ ψ σ b $ᵛ x = eval (Γ ▻ σ) (ψ ▷ x) b
  f             $ᵛ x = f ·ᵛ x

eval₀ : Term⁽⁾ -> Value⁽⁾
eval₀ = eval ε ø

mutual
  quoteᵛ : Value ∸> Term
  quoteᵛ  typeᵛ          = type
  quoteᵛ (piᵛ σ τₖ)      = π (quoteᵛ σ) (quoteᵏ τₖ)
  quoteᵛ (varᵛ v)        = var v
  quoteᵛ (suspᵛ Γ ψ σ b) = ƛ (norm Γ ψ σ) (norm (Γ ▻ σ) (keepᵉ ψ) b)
  quoteᵛ (f ·ᵛ x)        = quoteᵛ f · quoteᵛ x
  
  quoteᵏ : ∀ {n} -> Kripke n -> Term (suc n)
  quoteᵏ = quoteᵛ ∘ instᵏ

  norm : ∀ {n m} -> Con n -> m ↤ n -> Term n -> Term m
  norm Γ ψ = quoteᵛ ∘ eval Γ ψ

abstᵏ : ∀ {n m} -> Con (suc n) -> m ↤ n -> Value (suc n) -> Kripke m
abstᵏ Γ ψ = evalᵏ Γ ψ ∘ quoteᵛ

mutual
  infer : ∀ {n m} -> Con n -> m ↤ n -> Term n -> Maybe (Value m)
  infer Γ ψ  type   = return typeᵛ
  infer Γ ψ (π σ τ) = check Γ ψ σ typeᵛ >> check (Γ ▻ σ) (skipᵉ ψ ▷ fresh) τ typeᵛ >> return typeᵛ
  infer Γ ψ (var v) = return (eval Γ ψ (lookupᶜ v Γ))
  infer Γ ψ (ƛ σ b) = check Γ ψ σ typeᵛ >> return (suspᵛ Γ ψ σ b)
  infer Γ ψ (f · x) =
    infer Γ ψ f >>= λ
      { (suspᵛ Δ φ σ b) -> check Γ ψ x (eval Δ φ σ) >> infer (Δ ▻ σ) (φ ▷ eval Γ ψ x) b
      ; (piᵛ σ τₖ)      -> check Γ ψ x σ >> return (τₖ [ eval Γ ψ x ]ᵏ)
      ;  _              -> nothing
      }

  infer* : ∀ {n m} -> Con n -> m ↤ n -> Term n -> Maybe (Term m)
  infer* Γ ψ t = infer Γ ψ t >>= λ
    { (suspᵛ Δ φ σ b) -> π (norm Δ φ σ) <$> infer* (Δ ▻ σ) (keepᵉ φ) b
    ;  σ              -> just (quoteᵛ σ)
    }

  check : ∀ {n m} -> Con n -> m ↤ n -> Term n -> Value m -> Maybe ⊤
  check Γ ψ t σ = infer* Γ ψ t >>= λ σ′ -> _ <$> σ′ ≟ quoteᵛ σ

infer₀ : Term⁽⁾ -> Maybe Term⁽⁾
infer₀ = infer* ε ø

check₀ : Term⁽⁾ -> Value⁽⁾ -> Maybe ⊤
check₀ = check ε ø

typecheck : Term⁽⁾ -> Type⁽⁾ -> Maybe ⊤
typecheck t σ = check₀ σ typeᵛ >> check₀ t (eval₀ σ)



A : Term⁺
A = ƛ type
  $ ƛ (π (var fzero) type)
  $ ƛ (π (var (fsuc fzero)) (var (fsuc fzero) · var fzero))
  $ ƛ (var (fsuc (fsuc fzero)))
  $ var (fsuc fzero) · var fzero

Aᵀ : Type⁺
Aᵀ = π type
   $ π (π (var fzero) type) 
   $ π (π (var (fsuc fzero)) (var (fsuc fzero) · var fzero))
   $ π (var (fsuc (fsuc fzero)))
   $ var (fsuc (fsuc fzero)) · var fzero
  
test : infer₀ A ≡ just Aᵀ
test = refl
