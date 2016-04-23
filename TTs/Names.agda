-- That's the only unsafe thing.
{-# OPTIONS --no-positivity-check #-}

-- Variables in `Term` and `_⊢_` are well-scoped de Bruijn indices.
-- Variables in `Value` and `Raw` are raw de Bruijn levels.
-- We also trace variable names everywhere except for `Raw` which has straightforward α-equality.

open import Level renaming (zero to lzero; suc to lsuc) using (_⊔_; Lift)
open import Function hiding (_∋_; _⟨_⟩_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty
open import Data.Unit.Base using (⊤; tt)
open import Data.Bool.Base hiding (_≟_)
open import Data.Nat.Base as Nat hiding (_≟_; _⊔_)
open import Data.Fin renaming (zero to fzero; suc to fsuc) using (Fin; fromℕ; inject₁)
open import Data.String as String hiding (_++_; _≟_)
open import Data.Maybe as Maybe renaming (map to fmap) hiding (Any)
open import Data.Product renaming (map to pmap) hiding (,_)
open import Data.Vec hiding (_⊛_; _>>=_)
open import Category.Monad

open RawMonad {{...}} hiding (pure; zipWith)

infixr 4 ,_
infixl 1 _>>=ᵀ_ _>>=ᵗ_

infixr 6 ƛʳ_
infixl 7 _·ʳ_
infixl 5 _▻_∋_ _▷_
infix  4 _⊢_
infixl 2 _∋_

pattern ,_ y  = _ , y
pattern herer = here refl

instance
  maybeMonad : ∀ {α} -> RawMonad {α} Maybe
  maybeMonad = Maybe.monad

any : ∀ {n α} {A : Set α} -> (A -> Bool) -> Vec A n -> Bool
any p = foldr _ (λ x r -> p x ∨ r) false

∈→Fin : ∀ {n α} {A : Set α} {x} {xs : Vec A n} -> x ∈ xs -> Fin n
∈→Fin  here     = fzero
∈→Fin (there p) = fsuc (∈→Fin p)

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

  stringMEq : MEq String
  stringMEq = record { _≟_ = λ s t -> decToMaybe (s String.≟ t) }

_>>=ᵀ_ : ∀ {α β} {A : Set α} -> Maybe A -> (A -> Set β) -> Set β
nothing >>=ᵀ B = Lift ⊤
just x  >>=ᵀ B = B x

_>>=ᵗ_ : ∀ {α β} {A : Set α} {B : A -> Set β} -> (a : Maybe A) -> (∀ x -> B x) -> a >>=ᵀ B
nothing >>=ᵗ f = _
just x  >>=ᵗ f = f x

----------

Name : Set
Name = String

Names : ℕ -> Set
Names = Vec String

module TermWith A where
  infixr 6 ⟨_∶_⟩_ λ⟨_⟩_
  infixl 7 _·_

  mutual
    Type = Term

    data Term {l} (ns : Names l) : Set where
      pure   : A -> Term ns
      type   : Type ns
      ⟨_∶_⟩_ : ∀ n -> Type ns -> Type (n ∷ ns) -> Type ns
      devar  : ∀ {n} -> n ∈ ns -> Term ns
      λ⟨_⟩_  : ∀ n -> Term (n ∷ ns) -> Term ns
      _·_    : Term ns -> Term ns -> Term ns

  Term⁽⁾ : Set
  Term⁽⁾ = Term []

  Term⁺ : Set
  Term⁺ = ∀ {l} {ns : Names l} -> Term ns

  Type⁽⁾ = Term⁽⁾
  Type⁺  = Term⁺

module _ {A} where
  infixr 6 _⇒_

  open TermWith A

  index : ∀ {l} {ns : Names l} n {_ : T (any (n ==_) ns)} -> n ∈ ns
  index {ns = []}     n {()}
  index {ns = m ∷ ns} n {t}  with n String.≟ m
  ... | yes r rewrite r = here
  ... | no _            = there (index n {t})

  _⇒_ : ∀ {l} {ns : Names l} -> Type ns -> Type ("" ∷ ns) -> Type ns
  σ ⇒ τ = ⟨ "" ∶ σ ⟩ τ

  var : ∀ {l} {ns : Names l} n {_ : T (any (n ==_) ns)} -> Term ns
  var n {t} = devar (index n {t})

----------

mutual
  data Value : Set where
    typeᵛ : Value
    piᵛ   : Name  -> Value  -> Kripke -> Value
    varᵛ  : ℕ     -> Name   -> Value
    lamᵛ  : Name  -> Kripke -> Value
    _·ᵛ_  : Value -> Value  -> Value

  Kripke : Set
  Kripke = Value -> Value

_$ᵛ_ : Value -> Value -> Value
lamᵛ _ bₖ $ᵛ x = bₖ x
f         $ᵛ x = f ·ᵛ x

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

mutual
  quoteᵛ : ℕ -> Value -> Raw
  quoteᵛ l  typeᵛ       = typeʳ
  quoteᵛ l (piᵛ n σ τₖ) = πʳ (quoteᵛ l σ) (quoteᵏ l n τₖ)
  quoteᵛ l (varᵛ v _)   = varʳ v
  quoteᵛ l (lamᵛ n bₖ)  = ƛʳ (quoteᵏ l n bₖ)
  quoteᵛ l (f ·ᵛ x)     = quoteᵛ l f ·ʳ quoteᵛ l x

  quoteᵏ : ℕ -> Name -> Kripke -> Raw
  quoteᵏ l n k = quoteᵛ (suc l) (k (varᵛ l n))

----------

data Con : ∀ {l} -> Vec String l -> Set where
  ε     : Con []
  _▻_∋_ : ∀ {l} {ns : Names l} -> Con ns -> Value -> ∀ n -> Con (n ∷ ns)

data Env : ℕ -> Set where
  ø   : Env 0
  _▷_ : ∀ {n} -> Env n -> Value -> Env (suc n)

lookupᶜ : ∀ {l} {ns : Names l} -> Fin l -> Con ns -> Value
lookupᶜ  fzero   (Γ ▻ σ ∋ n) = σ
lookupᶜ (fsuc i) (Γ ▻ σ ∋ n) = lookupᶜ i Γ

lookupᵉ : ∀ {n} -> Fin n -> Env n -> Value
lookupᵉ  fzero   (ψ ▷ x) = x
lookupᵉ (fsuc i) (ψ ▷ x) = lookupᵉ i ψ

stopᵉ : ∀ {l} {ns : Names l} -> Con ns -> Env l
stopᵉ          ε          = ø
stopᵉ {suc l} (Γ ▻ σ ∋ n) = stopᵉ Γ ▷ varᵛ l n

mutual
  data _⊢_ {l} {ns : Names l} (Γ : Con ns) : Value -> Set where
    typeᵗ   : Γ ⊢ typeᵛ
    ⟨_∶_⟩ᵗ_ : ∀ n -> (σₜ : Γ ⊢ typeᵛ) -> Γ ▻ eval σₜ ∋ n ⊢ typeᵛ -> Γ ⊢ typeᵛ
    varᵗ    : ∀ v -> Γ ⊢ lookupᶜ v Γ
    λ⟨_⟩ᵗ_  : ∀ {m σ τₖ} n -> Γ ▻ σ ∋ n ⊢ τₖ (varᵛ l m) -> Γ ⊢ piᵛ m σ τₖ
    _·ᵗ_    : ∀ {n σ τₖ} -> Γ ⊢ piᵛ n σ τₖ -> (xₜ : Γ ⊢ σ) -> Γ ⊢ τₖ (eval xₜ)
    coeᵗ    : ∀ {σ τ} -> quoteᵛ l σ ≡ quoteᵛ l τ -> Γ ⊢ σ -> Γ ⊢ τ
    wkᵗ     : ∀ {σ} -> ε ⊢ σ -> Γ ⊢ σ

  ⟦_/_⟧ : ∀ {l σ} {ns : Names l} {Γ : Con ns} -> Env l -> Γ ⊢ σ -> Value
  ⟦ ψ / typeᵗ        ⟧ = typeᵛ
  ⟦ ψ / ⟨ n ∶ σ ⟩ᵗ τ ⟧ = piᵛ n ⟦ ψ / σ ⟧ ⟦ ψ / τ ⟧ᵏ
  ⟦ ψ / varᵗ v       ⟧ = lookupᵉ v ψ
  ⟦ ψ / λ⟨ n ⟩ᵗ b    ⟧ = lamᵛ n ⟦ ψ / b ⟧ᵏ
  ⟦ ψ / f ·ᵗ x       ⟧ = ⟦ ψ / f ⟧ $ᵛ ⟦ ψ / x ⟧
  ⟦ ψ / coeᵗ q t     ⟧ = ⟦ ψ / t ⟧
  ⟦ ψ / wkᵗ t        ⟧ = eval t

  ⟦_/_⟧ᵏ : ∀ {l n σ τ} {ns : Names l} {Γ : Con ns} -> Env l -> Γ ▻ σ ∋ n ⊢ τ -> Kripke
  ⟦ ψ / t ⟧ᵏ x = ⟦ ψ ▷ x / t ⟧

  eval : ∀ {l σ} {ns : Names l} {Γ : Con ns} -> Γ ⊢ σ -> Value
  eval {Γ = Γ} t = ⟦ stopᵉ Γ / t ⟧

----------

open TermWith (∃ (ε ⊢_))

coerceᵗ : ∀ {l σ τ} {ns : Names l} {Γ : Con ns} -> Γ ⊢ σ -> Maybe (Γ ⊢ τ)
coerceᵗ {l} {σ} {τ} t = flip coeᵗ t <$> quoteᵛ l σ ≟ quoteᵛ l τ

mutual
  infer : ∀ {l} {ns : Names l} {Γ : Con ns} -> Term ns -> Maybe (∃ (Γ ⊢_))
  infer (pure (, t))  = just (, wkᵗ t)
  infer  type         = return (, typeᵗ)
  infer (⟨ n ∶ σ ⟩ τ) = check σ typeᵛ >>= λ σₜ -> (λ τₜ -> , ⟨ n ∶ σₜ ⟩ᵗ τₜ) <$> check τ typeᵛ
  infer (devar v)     = return (, varᵗ (∈→Fin v))
  infer (λ⟨ n ⟩ b)    = nothing
  infer (f · x)       = infer f >>= λ
    { (piᵛ n σ τₖ , fₜ) -> (λ xₜ -> , fₜ ·ᵗ xₜ) <$> check x σ
    ;  _                -> nothing
    }

  check : ∀ {l} {ns : Names l} {Γ : Con ns} -> Term ns -> (σ : Value) -> Maybe (Γ ⊢ σ)
  check {l} (λ⟨ n ⟩ b) (piᵛ m σ τₖ) = λ⟨ n ⟩ᵗ_ <$> check b (τₖ (varᵛ l m))
  check      t          σ           = infer t >>= coerceᵗ ∘ proj₂

-- Double hidden-lambda bug.
typecheck : Term⁽⁾ -> Value -> Maybe Term⁺
typecheck t σ = (λ tₜ {_ _} -> pure (, tₜ)) <$> check t σ 

_∋_ : ∀ σ t -> _
σ ∋ t = check {Γ = ε} σ typeᵛ >>=ᵗ λ σₜ -> typecheck t (eval σₜ) >>=ᵗ id

----------

Iᵗ : Term⁺
Iᵗ = (⟨ "A" ∶ type ⟩ var "A" ⇒ var "A")
   ∋ λ⟨ "A" ⟩ λ⟨ "x" ⟩ var "x"

Aᵗ : Term⁺
Aᵗ = (⟨ "A" ∶ type ⟩
      ⟨ "B" ∶ var "A" ⇒ type ⟩
      (       ⟨ "x" ∶ var "A" ⟩ var "B" · var "x") ⇒
      ⟨ "x" ∶ var "A" ⟩
      var "B" · var "x")
   ∋ λ⟨ "A" ⟩ λ⟨ "B" ⟩ λ⟨ "f" ⟩ λ⟨ "x" ⟩ var "f" · var "x"

Sᵗ : Term⁺
Sᵗ = (⟨ "A" ∶ type ⟩
      ⟨ "B" ∶ var "A" ⇒ type ⟩
      ⟨ "C" ∶ ⟨ "x" ∶ var "A" ⟩ var "B" · var "x" ⇒ type ⟩
      (       ⟨ "x" ∶ var "A" ⟩ ⟨ "y" ∶ var "B" · var "x" ⟩ var "C" · var "x" · var "y") ⇒
      ⟨ "f" ∶ ⟨ "x" ∶ var "A" ⟩ var "B" · var "x" ⟩
      ⟨ "x" ∶ var "A" ⟩
      var "C" · var "x" · (var "f" · var "x"))
   ∋ λ⟨ "A" ⟩ λ⟨ "B" ⟩ λ⟨ "C" ⟩ λ⟨ "g" ⟩ λ⟨ "f" ⟩ λ⟨ "x" ⟩ var "g" · var "x" · (var "f" · var "x")

test₀ : Term⁺
test₀ = (⟨ "A" ∶ type ⟩ Iᵗ · type · (var "A" ⇒ var "A"))
      ∋ λ⟨ "A" ⟩ Aᵗ · (var "A" ⇒ var "A")
                    · (λ⟨ "" ⟩ (var "A" ⇒ var "A"))
                    · (Iᵗ · (var "A" ⇒ var "A"))
                    · (Iᵗ · var "A")

test₁ : Term⁺
test₁ = (⟨ "A" ∶ type ⟩ Iᵗ · type · (⟨ "x1" ∶ var "A" ⟩ var "A"))
      ∋ λ⟨ "A" ⟩ Aᵗ · (⟨ "x2" ∶ var "A" ⟩ var "A")
                    · (λ⟨ "x5" ⟩ (⟨ "x3" ∶ var "A" ⟩ var "A"))
                    · (Iᵗ · (⟨ "x4" ∶ var "A" ⟩ var "A"))
                    · (Iᵗ · var "A")

extr : Term⁽⁾ -> Maybe _
extr (pure p) = just p
extr  _       = nothing

test-Sᵗ : (extr Sᵗ >>=ᵗ quoteᵛ 0 ∘ eval ∘ proj₂)
        ≡ ƛʳ ƛʳ ƛʳ ƛʳ ƛʳ ƛʳ varʳ 3 ·ʳ varʳ 5 ·ʳ (varʳ 4 ·ʳ varʳ 5)
test-Sᵗ = refl

test-test₀ : (extr test₀ >>=ᵗ quoteᵛ 0 ∘ eval ∘ proj₂) ≡ ƛʳ ƛʳ varʳ 1
test-test₀ = refl
