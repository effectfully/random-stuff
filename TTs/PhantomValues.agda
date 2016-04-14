-- Raw values wrapped in a phantom type. The idea is nice, the result is ugly.
-- I don't want to write even trivial tests for this freak.

{-# OPTIONS --no-positivity-check --no-termination-check #-}

open import Level renaming (zero to lzero; suc to lsuc) using (_⊔_)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Unit.Base using (⊤; tt)
open import Data.Nat.Base  hiding (_≟_; _⊔_)
open import Data.Fin renaming (zero to fzero; suc to fsuc) using (Fin; fromℕ; toℕ; inject₁)
import Data.Fin.Properties as FinProp
open import Data.Maybe as Maybe renaming (map to fmap)
open import Data.Product renaming (map to pmap)
open import Category.Monad

open RawMonad {{...}} hiding (zipWith)

infixr 5 ƛ_
infixl 6 _·_
infixl 5 _▻_
infix  4 _⊢_
infixl 8 _[_]ᵏ _⟦_⟧ᵏ

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

record Nil {α} : Set α where
  constructor []

infixl 6 _^_

_^_ : ∀ {α} -> Set α -> ℕ -> Set α
A ^ 0     = Nil
A ^ suc n = A × A ^ n

map : ∀ {n α β} {A : Set α} {B : Set β} -> (A -> B) -> A ^ n -> B ^ n
map {0}     f  []      = []
map {suc n} f (x , xs) = f x , map f xs

zipWith : ∀ {n α β γ} {A : Set α} {B : Set β} {C : Set γ}
        -> (A -> B -> C) -> A ^ n -> B ^ n -> C ^ n
zipWith {0}     f  []       []      = []
zipWith {suc n} f (x , xs) (y , ys) = f x y , zipWith f xs ys

Fold₁ : ∀ {n α} -> Set α ^ suc n -> Set α
Fold₁ {0}     (A , []) = A
Fold₁ {suc n} (A , As) = A -> Fold₁ As

record _<_> (A : Set) (n : ℕ) : Set where
  constructor tag
  field detag : A
open _<_> public

lift : ∀ n {As : Set ^ suc n} {ms : ℕ ^ suc n} -> Fold₁ As -> Fold₁ (zipWith _<_> As ms)
lift  0      y = tag y
lift (suc n) f = lift n ∘ f ∘ detag

lower# : ∀ n {As : Set ^ suc n} {ms : ℕ ^ suc n} -> Fold₁ (zipWith _<_> As ms) -> Fold₁ As
lower#  0      y = detag y
lower# (suc n) f = lower# n ∘ f ∘ tag

wk : ∀ {n A} -> A < n > -> A < suc n >
wk = lift 1 id

trustFromℕ : ∀ {m} -> ℕ -> Fin m
trustFromℕ {0}      n      = undefined where postulate undefined : _
trustFromℕ {suc m}  0      = fzero
trustFromℕ {suc m} (suc n) = fsuc (trustFromℕ n)

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
  data Value : Set where
    typeᵛ : Value
    piᵛ   : Value  -> Kripke -> Value
    varᵛ  : ℕ      -> Value
    lamᵛ  : Kripke -> Value
    _·ᵛ_  : Value  -> Value  -> Value

  Kripke : Set
  Kripke = Value -> Value

kripke# : ∀ {n} -> (Value < n > -> Value < n >) -> Kripke < n >
kripke# = tag ∘ lower# 1

typeᵗ : ∀ {n} -> Value < n >
typeᵗ = lift 0 typeᵛ

piᵗ : ∀ {n} -> Value < n > -> Kripke < n > -> Value < n >
piᵗ = lift 2 piᵛ

lamᵗ : ∀ {n} -> Kripke < n > -> Value < n >
lamᵗ = lift 1 lamᵛ

_·ᵗ_ : ∀ {n} -> Value < n > -> Value < n > -> Value < n >
_·ᵗ_ = lift 2 _·ᵛ_

fresh : ∀ {n} -> Value < suc n >
fresh {n} = lift 0 (varᵛ n)

_[_]ᵏ′ : ∀ {n m} -> Kripke < n > -> Value < m > -> Value < m >
_[_]ᵏ′ = lift 2 id

_[_]ᵏ : ∀ {n} -> Kripke < n > -> Value < n > -> Value < n >
_[_]ᵏ = _[_]ᵏ′

instᵏ : ∀ {n} -> Kripke < n > -> Value < suc n >
instᵏ k = k [ fresh ]ᵏ′

_$ᵗ_ : ∀ {n} -> Value < n > -> Value < n > -> Value < n >
tag (lamᵛ bₖ) $ᵗ x = tag bₖ [ x ]ᵏ
f             $ᵗ x = f ·ᵗ x

----------

mutual
  quoteᵛ : ∀ {n} -> Value -> Term n
  quoteᵛ      typeᵛ     = type
  quoteᵛ     (piᵛ σ τₖ) = π (quoteᵛ σ) (quoteᵏ τₖ)
  quoteᵛ {n} (varᵛ v)   = var (trustFromℕ (n ∸ v ∸ 1))
  quoteᵛ     (lamᵛ bₖ)  = ƛ (quoteᵏ bₖ)
  quoteᵛ     (f ·ᵛ x)   = quoteᵛ f · quoteᵛ x

  quoteᵏ : ∀ {n} -> Kripke -> Term (suc n)
  quoteᵏ = quoteᵗ ∘ instᵏ ∘ tag

  quoteᵗ : ∀ {n} -> Value < n > -> Term n
  quoteᵗ = quoteᵛ ∘ detag

----------

data Con : ℕ -> Set where
  ε   : Con 0
  _▻_ : ∀ {n} -> Con n -> Value < n > -> Con (suc n)

data Env : ℕ -> Set where
  ø   : Env 0
  _▷_ : ∀ {n} -> Env n -> Value -> Env (suc n)

lookupᶜ : ∀ {n} -> Fin n -> Con n -> Value < n >
lookupᶜ  fzero   (Γ ▻ σ) = wk  σ
lookupᶜ (fsuc i) (Γ ▻ σ) = wk (lookupᶜ i Γ)

_↦_ : ℕ -> ℕ -> Set
n ↦ m = Env n < m >

øᵗ : ∀ {m} -> 0 ↦ m
øᵗ = lift 0 ø

_▷ᵗ_ : ∀ {n m} -> n ↦ m -> Value < m > -> suc n ↦ m
_▷ᵗ_ = lift 2 _▷_

keepᵉ : ∀ {n m} -> n ↦ m -> suc n ↦ suc m
keepᵉ ψ = wk ψ ▷ᵗ fresh

stopᵉ : ∀ {n} -> n ↦ n
stopᵉ {0}     = øᵗ
stopᵉ {suc n} = keepᵉ stopᵉ

rawLookupᵉ : ∀ {n} -> Fin n -> Env n -> Value
rawLookupᵉ  fzero   (ψ ▷ x) = x
rawLookupᵉ (fsuc i) (ψ ▷ x) = rawLookupᵉ i ψ

lookupᵉ : ∀ {n m} -> Fin n -> n ↦ m -> Value < m >
lookupᵉ = lift 1 ∘ rawLookupᵉ

----------

mutual
  data _⊢_ {n} Γ : Value < n > -> Set where
    type⁺ : Γ ⊢ typeᵗ
    π⁺    : (σₜ : Γ ⊢ typeᵗ) -> Γ ▻ eval σₜ ⊢ typeᵗ -> Γ ⊢ typeᵗ
    var⁺  : ∀ v -> Γ ⊢ lookupᶜ v Γ
    ƛ⁺    : ∀ {σ} {τₖ : Kripke < n >} -> Γ ▻ σ ⊢ instᵏ τₖ -> Γ ⊢ piᵗ σ τₖ
    _·⁺_  : ∀ {σ} {τₖ : Kripke < n >} -> Γ ⊢ piᵗ σ τₖ -> (xₜ : Γ ⊢ σ) -> Γ ⊢ τₖ ⟦ xₜ ⟧ᵏ
    coe⁺  : ∀ {σ τ} -> quoteᵗ σ ≡ quoteᵗ τ -> Γ ⊢ σ -> Γ ⊢ τ

  ⟦_/_⟧ : ∀ {n m σ} {Γ : Con n} -> n ↦ m -> Γ ⊢ σ -> Value < m >
  ⟦ ψ / type⁺    ⟧ = typeᵗ
  ⟦ ψ / π⁺ σ τ   ⟧ = piᵗ ⟦ ψ / σ ⟧ ⟦ ψ / τ ⟧ᵏ
  ⟦ ψ / var⁺ v   ⟧ = lookupᵉ v ψ
  ⟦ ψ / ƛ⁺ b     ⟧ = lamᵗ ⟦ ψ / b ⟧ᵏ
  ⟦ ψ / f ·⁺ x   ⟧ = ⟦ ψ / f ⟧ $ᵗ ⟦ ψ / x ⟧
  ⟦ ψ / coe⁺ q t ⟧ = ⟦ ψ / t ⟧

  ⟦_/_⟧ᵏ : ∀ {n m σ τ} {Γ : Con n} -> n ↦ m -> Γ ▻ σ ⊢ τ -> Kripke < m >
  ⟦ ψ / t ⟧ᵏ = kripke# λ x -> ⟦ ψ ▷ᵗ x / t ⟧

  eval : ∀ {n σ} {Γ : Con n} -> Γ ⊢ σ -> Value < n >
  eval t = ⟦ stopᵉ / t ⟧
  
  _⟦_⟧ᵏ : ∀ {n σ} {Γ : Con n} -> Kripke < n > -> Γ ⊢ σ -> Value < n >
  k ⟦ x ⟧ᵏ = k [ eval x ]ᵏ

----------

coerce⁺ : ∀ {n σ τ} {Γ : Con n} -> Γ ⊢ σ -> Maybe (Γ ⊢ τ)
coerce⁺ {σ = σ} {τ} t = flip coe⁺ t <$> quoteᵗ σ ≟ quoteᵗ τ

mutual
  infer : ∀ {n} {Γ : Con n} -> Term n -> Maybe (∃ λ σ -> Γ ⊢ tag σ)
  infer  type   = return (, type⁺)
  infer (π σ τ) = check σ typeᵛ >>= λ σ₊ -> (λ τ₊ -> , π⁺ σ₊ τ₊) <$> check τ typeᵛ
  infer (var v) = return (, var⁺ v)
  infer (ƛ b)   = nothing
  infer (f · x) = infer f >>= λ
    { (piᵛ σ τₖ , f₊) -> (λ x₊ -> , f₊ ·⁺ x₊) <$> check x σ
    ;  _              -> nothing
    }

  check : ∀ {n} {Γ : Con n} -> Term n -> (σ : Value) -> Maybe (Γ ⊢ tag σ)
  check (ƛ b) (piᵛ σ τₖ) = ƛ⁺ <$> checkᵗ b (instᵏ (tag τₖ))
  check  t     σ         = infer t >>= coerce⁺ ∘ proj₂

  checkᵗ : ∀ {n} {Γ : Con n} -> Term n -> (σ : Value < n >) -> Maybe (Γ ⊢ σ)
  checkᵗ t = check t ∘ detag
