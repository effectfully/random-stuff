-- That's the only unsafe thing.
{-# OPTIONS --no-positivity-check #-}

-- Variables in `Term` and `_⊢_` are well-scoped de Bruijn indices.
-- Variables in `Value` and `Raw` are raw de Bruijn levels.

open import Level renaming (zero to lzero; suc to lsuc) using (_⊔_; Lift)
open import Function hiding (_∋_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty
open import Data.Unit.Base using (⊤; tt)
open import Data.Nat.Base as Nat  hiding (_≟_; _⊔_)
open import Data.Fin renaming (zero to fzero; suc to fsuc) using (Fin; fromℕ; inject₁)
open import Data.Maybe as Maybe renaming (map to fmap)
open import Data.Product renaming (map to pmap) hiding (,_)
open import Category.Monad

open RawMonad {{...}} hiding (pure; zipWith)

infixr 4 ,_

infixl 5 _▷_
infix  4 _⊢_
infixl 2 _∋_

pattern ,_ y = _ , y

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
  ⊥MEq : MEq ⊥
  ⊥MEq = record { _≟_ = λ() }

  natMEq : MEq ℕ
  natMEq = record { _≟_ = λ n m -> decToMaybe (n Nat.≟ m) }

_>>=ᵀ_ : ∀ {α β} {A : Set α} -> Maybe A -> (A -> Set β) -> Set β
nothing >>=ᵀ B = Lift ⊤
just x  >>=ᵀ B = B x

_>>=ᵗ_ : ∀ {α β} {A : Set α} {B : A -> Set β} -> (a : Maybe A) -> (∀ x -> B x) -> a >>=ᵀ B
nothing >>=ᵗ f = _
just x  >>=ᵗ f = f x

fromℕ⁻ : ∀ {m} n -> Fin (suc n + m)
fromℕ⁻  0      = fromℕ _
fromℕ⁻ (suc n) = inject₁ (fromℕ⁻ n)

----------

module TermWith A where
  infixr 5 ƛ_
  infixl 6 _·_

  mutual
    Type = Term

    data Term n : Set where
      pure : A            -> Term  n
      type : Type  n
      π    : Type  n      -> Type (suc n) -> Type n
      var  : Fin   n      -> Term  n
      ƛ_   : Term (suc n) -> Term  n
      _·_  : Term  n      -> Term  n      -> Term n

  Term⁽⁾ : Set
  Term⁽⁾ = Term 0

  Term⁺ : Set
  Term⁺ = ∀ {n} -> Term n

  Type⁽⁾ = Term⁽⁾
  Type⁺  = Term⁺

module _ {A} where
  infixr 5 _⇒_

  open TermWith A

  Bind : ℕ -> ℕ -> Set
  Bind n  0      = Term n
  Bind n (suc m) = (∀ {p} -> Term (suc n + p)) -> Bind (suc n) m

  instᵇ : ∀ {n m} -> Bind n (suc m) -> Bind (suc n) m
  instᵇ {n} b = b (var (fromℕ⁻ n))

  pi : ∀ {n} -> Type n -> Bind n 1 -> Type n
  pi σ = π σ ∘ instᵇ

  _⇒_ : ∀ {n} -> Type n -> Type (suc n) -> Type n
  σ ⇒ τ = pi σ λ _ -> τ

  lam : ∀ {n} m -> Bind n m -> Term n
  lam  0      b = b
  lam (suc m) b = ƛ (lam m (instᵇ b))

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

_$ᵛ_ : Value -> Value -> Value
lamᵛ bₖ $ᵛ x = bₖ x
f       $ᵛ x = f ·ᵛ x

data Env : ℕ -> Set where
  ø   : Env 0
  _▷_ : ∀ {n} -> Env n -> Value -> Env (suc n)

Con = Env

stopᵉ : ∀ {n} -> Env n
stopᵉ {0}     = ø
stopᵉ {suc n} = stopᵉ ▷ varᵛ n

lookupᵉ : ∀ {n} -> Fin n -> Env n -> Value
lookupᵉ  fzero   (ψ ▷ x) = x
lookupᵉ (fsuc i) (ψ ▷ x) = lookupᵉ i ψ

lookupᶜ = lookupᵉ

----------

data Raw : Set where
  typeʳ : Raw
  πʳ    : Raw -> Raw -> Raw
  varʳ  : ℕ   -> Raw
  ƛʳ_   : Raw -> Raw
  _·ʳ_  : Raw -> Raw -> Raw

instance
  rawMEq : MEq Raw
  rawMEq = record { _≟_ = go } where
    go : MEquates Raw
    go  typeʳ      typeʳ     = just refl
    go (πʳ σ₁ τ₁) (πʳ σ₂ τ₂) = cong₂ πʳ <$> go σ₁ σ₂ ⊛ go τ₁ τ₂ 
    go (varʳ v₁)  (varʳ v₂)  = cong varʳ <$> v₁ ≟ v₂
    go (ƛʳ b₁)    (ƛʳ b₂)    = cong ƛʳ_ <$> go b₁ b₂
    go (f₁ ·ʳ x₁) (f₂ ·ʳ x₂) = cong₂ _·ʳ_ <$> go f₁ f₂ ⊛ go x₁ x₂
    go  _          _         = nothing

lengthᵉ : ∀ {n} -> Env n -> ℕ
lengthᵉ {n} _ = n

mutual
  quoteᵛ : ∀ n -> Value -> Raw
  quoteᵛ n  typeᵛ     = typeʳ
  quoteᵛ n (piᵛ σ τₖ) = πʳ (quoteᵛ n σ) (quoteᵏ n τₖ)
  quoteᵛ n (varᵛ v)   = varʳ v
  quoteᵛ n (lamᵛ bₖ)  = ƛʳ (quoteᵏ n bₖ)
  quoteᵛ n (f ·ᵛ x)   = quoteᵛ n f ·ʳ quoteᵛ n x

  quoteᵏ : ∀ n -> Kripke -> Raw
  quoteᵏ n k = quoteᵛ (suc n) (k (varᵛ n))

mutual
  data _⊢_ {n} (Γ : Con n) : Value -> Set where
    typeᵗ : Γ ⊢ typeᵛ
    πᵗ    : (σₜ : Γ ⊢ typeᵛ) -> Γ ▷ eval σₜ ⊢ typeᵛ -> Γ ⊢ typeᵛ
    varᵗ  : ∀ v -> Γ ⊢ lookupᶜ v Γ
    ƛᵗ    : ∀ {σ τₖ} -> Γ ▷ σ ⊢ τₖ (varᵛ n) -> Γ ⊢ piᵛ σ τₖ
    _·ᵗ_  : ∀ {σ τₖ} -> Γ ⊢ piᵛ σ τₖ -> (xₜ : Γ ⊢ σ) -> Γ ⊢ τₖ (eval xₜ)
    coeᵗ  : ∀ {σ τ} -> quoteᵛ n σ ≡ quoteᵛ n τ -> Γ ⊢ σ -> Γ ⊢ τ
    wkᵗ   : ∀ {σ} -> ø ⊢ σ -> Γ ⊢ σ

  ⟦_/_⟧ : ∀ {n σ} {Γ : Con n} -> Env n -> Γ ⊢ σ -> Value
  ⟦ ψ / typeᵗ    ⟧ = typeᵛ
  ⟦ ψ / πᵗ σ τ   ⟧ = piᵛ ⟦ ψ / σ ⟧ ⟦ ψ / τ ⟧ᵏ
  ⟦ ψ / varᵗ v   ⟧ = lookupᵉ v ψ
  ⟦ ψ / ƛᵗ b     ⟧ = lamᵛ ⟦ ψ / b ⟧ᵏ
  ⟦ ψ / f ·ᵗ x   ⟧ = ⟦ ψ / f ⟧ $ᵛ ⟦ ψ / x ⟧
  ⟦ ψ / coeᵗ q t ⟧ = ⟦ ψ / t ⟧
  ⟦ ψ / wkᵗ t    ⟧ = eval t

  ⟦_/_⟧ᵏ : ∀ {n σ τ} {Γ : Con n} -> Env n -> Γ ▷ σ ⊢ τ -> Kripke
  ⟦ ψ / t ⟧ᵏ x = ⟦ ψ ▷ x / t ⟧

  eval : ∀ {n σ} {Γ : Con n} -> Γ ⊢ σ -> Value
  eval t = ⟦ stopᵉ / t ⟧

----------

open TermWith (∃ (ø ⊢_)) public

coerceᵗ : ∀ {n σ τ} {Γ : Con n} -> Γ ⊢ σ -> Maybe (Γ ⊢ τ)
coerceᵗ {n} {σ} {τ} t = flip coeᵗ t <$> quoteᵛ n σ ≟ quoteᵛ n τ

mutual
  infer : ∀ {n} {Γ : Con n} -> Term n -> Maybe (∃ (Γ ⊢_))
  infer (pure (, t)) = just (, wkᵗ t)
  infer  type        = return (, typeᵗ)
  infer (π σ τ)      = check σ typeᵛ >>= λ σₜ -> (λ τₜ -> , πᵗ σₜ τₜ) <$> check τ typeᵛ
  infer (var v)      = return (, varᵗ v)
  infer (ƛ b)        = nothing
  infer (f · x)      = infer f >>= λ
    { (piᵛ σ τₖ , fₜ) -> (λ xₜ -> , fₜ ·ᵗ xₜ) <$> check x σ
    ;  _              -> nothing
    }

  check : ∀ {n} {Γ : Con n} -> Term n -> (σ : Value) -> Maybe (Γ ⊢ σ)
  check {n} (ƛ b) (piᵛ σ τₖ) = ƛᵗ <$> check b (τₖ (varᵛ n))
  check      t     σ         = infer t >>= coerceᵗ ∘ proj₂

typecheck : Term⁽⁾ -> Value -> Maybe Term⁺
typecheck t σ = (λ tₜ {_} -> pure (, tₜ)) <$> check t σ 

_∋_ : ∀ σ t -> _
σ ∋ t = check {Γ = ø} σ typeᵛ >>=ᵗ λ σₜ -> typecheck t (eval σₜ) >>=ᵗ id

----------

Iᵗ : Term⁺
Iᵗ = (pi type λ A → A ⇒ A)
   ∋ lam 2 λ A x → x

Kᵗ : Term⁺
Kᵗ = (pi type λ A
   → pi (A ⇒ type) λ B
   → pi A λ x
   → B · x
   ⇒ A)
   ∋ lam 4 λ A B x y → x

Aᵗ : Term⁺
Aᵗ = (pi type λ A
   → pi (A ⇒ type) λ B
   → (pi A λ x → B · x)
   ⇒ pi A λ x
   → B · x)
   ∋ lam 4 λ A B f x → f · x

Sᵗ : Term⁺
Sᵗ = (pi type λ A
   → pi (A ⇒ type) λ B
   → pi (pi A λ x → B · x ⇒ type) λ C
   → (pi A λ x → pi (B · x) λ y → C · x · y)
   ⇒ pi (pi A λ x → B · x) λ f
   → pi A λ x
   → C · x · (f · x))
   ∋ lam 6 λ A B C g f x → g · x · (f · x)

test : Term⁺
test = (pi type λ A → Iᵗ · type · A ⇒ A)
     ∋ lam 1 λ A → Aᵗ · (A ⇒ A) · (ƛ A ⇒ A) · (Iᵗ · (A ⇒ A)) · (Iᵗ · A)
