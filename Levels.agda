-- In order to type check this file you need Diff.agda in the same folder.
-- It's a type checker for a basic dependent type theory
-- that uses de Bruijn levels rather than de Bruijn indices.

{-# OPTIONS --no-positivity-check --no-termination-check #-}

open import Level renaming (zero to lzero; suc to lsuc) using (_⊔_)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Unit.Base using (⊤; tt)
open import Data.Nat.Base  hiding (_≟_; _⊔_)
open import Data.Fin renaming (zero to fzero; suc to fsuc) using (Fin; fromℕ)
import Data.Fin.Properties as FinProp
open import Data.Maybe as Maybe renaming (map to fmap)
open import Data.Product
open import Category.Monad

open import Diff

open RawMonad {{...}}

infixr 5 ƛ_
infixl 6 _·_
infixl 5 _▻_
infix  4 _⊢_
infixl 8 _[_]ᵏ _⟦_⟧ᵏ

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

Weakensk : (ℕ -> Set) -> (ℕ -> ℕ) -> Set
Weakensk Fam k = ∀ {n} -> Fam n -> Fam (k n)

Weakens : (ℕ -> Set) -> Set
Weakens Fam = ∀ {n} m -> Fam n -> Fam (m + n)

----------

mutual
  Type = Term

  data Term n : Set where
    type : Type  n
    π    : Type  n      -> Type (suc n) -> Type n
    var  : Fin   n      -> Term  n
    ƛ_   : Term (suc n) -> Term  n
    _·_  : Term  n      -> Term  n      -> Term n

Term⁽⁾ : Set
Term⁽⁾ = Term 0

Term⁺ : Set
Term⁺ = ∀ n -> Term n

Type⁽⁾ = Term⁽⁾
Type⁺  = Term⁺

instance
  termMEq : Fam MEq Term
  termMEq = record { _≟_ = go } where
    go : Fam MEquates Term
    go  type      type     = just refl
    go (π σ₁ τ₁) (π σ₂ τ₂) = cong₂ π <$> go σ₁ σ₂ ⊛ go τ₁ τ₂ 
    go (var v₁)  (var v₂)  = cong var <$> v₁ ≟ v₂
    go (ƛ b₁)    (ƛ b₂)    = cong ƛ_ <$> go b₁ b₂
    go (f₁ · x₁) (f₂ · x₂) = cong₂ _·_ <$> go f₁ f₂ ⊛ go x₁ x₂
    go  _         _        = nothing

----------

mutual
  data Value n : Set where
    typeᵛ : Value  n
    piᵛ   : Value  n -> Kripke n -> Value n
    varᵛ  : Fin    n -> Value  n
    lamᵛ  : Kripke n -> Value  n
    _·ᵛ_  : Value  n -> Value  n -> Value n

  Kripke : ℕ -> Set
  Kripke n = ∀ {k} -> Diff k -> Value (k n) -> Value (k n)

Value⁽⁾ : Set
Value⁽⁾ = Value 0

fresh : ∀ {n} -> Value (suc n)
fresh = varᵛ (fromℕ _)

_[_]ᵏ : ∀ {n} -> Kripke n -> Value n -> Value n
k [ t ]ᵏ = k dzero t

instᵏ : ∀ {n} -> Kripke n -> Value (suc n)
instᵏ k = k done fresh

_$ᵛ_ : ∀ {n} -> Value n -> Value n -> Value n
lamᵛ bₖ $ᵛ x = bₖ [ x ]ᵏ
f       $ᵛ x = f ·ᵛ x

mutual
  quoteᵛ : Value ∸> Term
  quoteᵛ  typeᵛ     = type
  quoteᵛ (piᵛ σ τₖ) = π (quoteᵛ σ) (quoteᵏ τₖ)
  quoteᵛ (varᵛ v)   = var v
  quoteᵛ (lamᵛ bₖ)  = ƛ (quoteᵏ bₖ)
  quoteᵛ (f ·ᵛ x)   = quoteᵛ f · quoteᵛ x
  
  quoteᵏ : ∀ {n} -> Kripke n -> Term (suc n)
  quoteᵏ = quoteᵛ ∘ instᵏ

data Con : ℕ -> Set where
  ε   : Con 0
  _▻_ : ∀ {n} -> Con n -> Value n -> Con (suc n)

data _↤_ m : ℕ -> Set where
  ø   : m ↤ 0
  _▷_ : ∀ {n} -> m ↤ n -> Value m -> m ↤ suc n

_↦_ = flip _↤_

module _ {k} (d : Diff k) where
  wkdᵏ : Weakensk Kripke k
  wkdᵏ k d′ = k (d′ ∘ᵈ d)

  wkdᵛ : Weakensk Value k
  wkdᵛ  typeᵛ     = typeᵛ
  wkdᵛ (piᵛ σ τₖ) = piᵛ (wkdᵛ σ) (wkdᵏ τₖ)
  wkdᵛ (varᵛ v)   = varᵛ (injectd d v)
  wkdᵛ (lamᵛ bₖ)  = lamᵛ (wkdᵏ bₖ)
  wkdᵛ (f ·ᵛ x)   = wkdᵛ f ·ᵛ wkdᵛ x

  wkdᵉ : Fam (flip Weakensk k) _↦_
  wkdᵉ  ø      = ø
  wkdᵉ (ψ ▷ x) = wkdᵉ ψ ▷ wkdᵛ x

lookupᵉ : ∀ {n m} -> Fin n -> n ↦ m -> Value m
lookupᵉ  fzero   (ψ ▷ x) = x
lookupᵉ (fsuc i) (ψ ▷ x) = lookupᵉ i ψ

lookupdᶜ : ∀ {k n} -> Diff k -> Fin n -> Con n -> Value (k n)
lookupdᶜ d  fzero   (Γ ▻ x) = wkdᵛ (dsucʳ d) x
lookupdᶜ d (fsuc v) (Γ ▻ x) = lookupdᶜ (dsucʳ d) v Γ

lookupᶜʳ : ∀ {n} -> Fin n -> Con n -> Value n
lookupᶜʳ = lookupdᶜ dzero ∘ revert

skipᵉ : ∀ {n m} -> n ↦ m -> n ↦ suc m
skipᵉ = wkdᵉ done

keepᵉ : ∀ {n m} -> n ↦ m -> suc n ↦ suc m
keepᵉ ψ = skipᵉ ψ ▷ fresh

stopᵉ : ∀ {n} -> n ↦ n
stopᵉ {0}     = ø
stopᵉ {suc n} = keepᵉ stopᵉ

----------

mutual
  data _⊢_ {n} Γ : Value n -> Set where
    typeᵗ : Γ ⊢ typeᵛ
    πᵗ    : (σₜ : Γ ⊢ typeᵛ) -> Γ ▻ eval σₜ ⊢ typeᵛ -> Γ ⊢ typeᵛ
    varᵗ  : ∀ v -> Γ ⊢ lookupᶜʳ v Γ
    ƛᵗ    : ∀ {σ} {τₖ : Kripke n} -> Γ ▻ σ ⊢ instᵏ τₖ -> Γ ⊢ piᵛ σ τₖ
    _·ᵗ_  : ∀ {σ} {τₖ : Kripke n} -> Γ ⊢ piᵛ σ τₖ -> (xₜ : Γ ⊢ σ) -> Γ ⊢ τₖ ⟦ xₜ ⟧ᵏ
    coeᵗ  : ∀ {σ τ} -> quoteᵛ σ ≡ quoteᵛ τ -> Γ ⊢ σ -> Γ ⊢ τ

  ⟦_/_⟧ : ∀ {n m σ} {Γ : Con n} -> n ↦ m -> Γ ⊢ σ -> Value m
  ⟦ ψ / typeᵗ    ⟧ = typeᵛ
  ⟦ ψ / πᵗ σ τ   ⟧ = piᵛ ⟦ ψ / σ ⟧ ⟦ ψ / τ ⟧ᵏ
  ⟦ ψ / varᵗ v   ⟧ = lookupᵉ (revert v) ψ
  ⟦ ψ / ƛᵗ b     ⟧ = lamᵛ ⟦ ψ / b ⟧ᵏ
  ⟦ ψ / f ·ᵗ x   ⟧ = ⟦ ψ / f ⟧ $ᵛ ⟦ ψ / x ⟧
  ⟦ ψ / coeᵗ q t ⟧ = ⟦ ψ / t ⟧

  ⟦_/_⟧ᵏ : ∀ {n m σ τ} {Γ : Con n} -> n ↦ m -> Γ ▻ σ ⊢ τ -> Kripke m
  ⟦ ψ / t ⟧ᵏ d x = ⟦ wkdᵉ d ψ ▷ x / t ⟧

  eval : ∀ {n σ} {Γ : Con n} -> Γ ⊢ σ -> Value n
  eval t = ⟦ stopᵉ / t ⟧
  
  _⟦_⟧ᵏ : ∀ {n σ} {Γ : Con n} -> Kripke n -> Γ ⊢ σ -> Value n
  k ⟦ x ⟧ᵏ = k [ eval x ]ᵏ

coerceᵗ : ∀ {n σ τ} {Γ : Con n} -> Γ ⊢ σ -> Maybe (Γ ⊢ τ)
coerceᵗ {σ = σ} {τ} t = flip coeᵗ t <$> quoteᵛ σ ≟ quoteᵛ τ

mutual
  infer : ∀ {n} {Γ : Con n} -> Term n -> Maybe (∃ (Γ ⊢_))
  infer  type   = return (, typeᵗ)
  infer (π σ τ) = check σ typeᵛ >>= λ σₜ -> (λ τₜ -> , πᵗ σₜ τₜ) <$> check τ typeᵛ
  infer (var v) = return (, varᵗ v)
  infer (ƛ b)   = nothing
  infer (f · x) = infer f >>= λ
    { (piᵛ σ τₖ , fₜ) -> (λ xₜ -> , fₜ ·ᵗ xₜ) <$> check x σ
    ;  _              -> nothing
    }
  check : ∀ {n} {Γ : Con n} -> Term n -> (σ : Value n) -> Maybe (Γ ⊢ σ)
  check (ƛ b) (piᵛ σ τₖ) = ƛᵗ <$> check b (instᵏ τₖ)
  check  t     σ         = infer t >>= coerceᵗ ∘ proj₂

typecheck : Term⁽⁾ -> Type⁽⁾ -> Maybe Term⁽⁾
typecheck t σ = check {Γ = ε} σ typeᵛ >>= fmap (quoteᵛ ∘ eval {Γ = ε}) ∘ check t ∘ eval

I : Term⁽⁾
I = ƛ ƛ var (fsuc fzero)

Iᵗ : Type⁽⁾
Iᵗ = π type $ π (var fzero) (var fzero)

A : Term⁽⁾
A = ƛ ƛ ƛ ƛ var (fsuc (fsuc fzero)) · var (fsuc (fsuc (fsuc fzero)))

Aᵗ : Type⁽⁾
Aᵗ = π type
   $ π (π (var fzero) type) 
   $ π (π (var fzero) (var (fsuc fzero) · var (fsuc (fsuc fzero))))
   $ π (var fzero)
   $ var (fsuc fzero) · var (fsuc (fsuc (fsuc fzero)))

test₁ : typecheck I Iᵗ ≡ just I
test₁ = refl

test₂ : typecheck A Aᵗ ≡ just A
test₂ = refl
