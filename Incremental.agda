open import Function hiding (_∋_)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Relation.Binary hiding (_⇒_)
open import Data.Unit.Base
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Fin renaming (zero to fzero; suc to fsuc) using (Fin)
open import Data.Maybe
open import Data.Product
open import Data.Vec hiding (_>>=_; _∈_; _⊛_)
open import Category.Monad
open module Silly {α} = RawMonad (monad {α}) hiding (_>>_)

infixr 6 _⇒_
infixl 5 _▻_ _▻▻_
infix  4 _∈_ _⊢_
infix  3 vs_
infixr 3 ƛ_
infixl 6 _·_
infix  5 _≟ᵗ_
infix  2 _∋_
infixr 1 _>>_

module _ m where
  data Syntax n : Set where
    free : Fin m -> Syntax n
    var  : Fin n -> Syntax n
    ƛ_   : Syntax (suc n) -> Syntax n
    _·_  : Syntax n -> Syntax n -> Syntax n

data Type : Set where
  ⋆   : Type 
  _⇒_ : Type -> Type -> Type

data Con : ℕ -> Set where
  ε   : Con 0
  _▻_ : ∀ {n} -> Con n -> Type -> Con (suc n)

data _∈_ σ : ∀ {n} -> Con n -> Set where
  vz  : ∀ {n}   {Γ : Con n} -> σ ∈ Γ ▻ σ
  vs_ : ∀ {n τ} {Γ : Con n} -> σ ∈ Γ     -> σ ∈ Γ ▻ τ 

data _⊢_ {n} (Γ : Con n) : Type -> Set where
  var : ∀ {σ}   -> σ ∈ Γ     -> Γ ⊢ σ
  ƛ_  : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _·_ : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ

Syntax⁽⁾ : ℕ -> Set
Syntax⁽⁾ m = Syntax m 0

Term⁽⁾ : Type -> Set
Term⁽⁾ σ = ε ⊢ σ

Term⁺ : Type -> Set
Term⁺ σ = ∀ {n} {Γ : Con n} -> Γ ⊢ σ

_▻▻_ : ∀ {n m} -> Con m -> Con n -> Con (n + m)
Δ ▻▻  ε      = Δ
Δ ▻▻ (Γ ▻ σ) = (Δ ▻▻ Γ) ▻ σ

wkᵛ : ∀ {n m σ} {Γ : Con n} {Δ : Con m} -> σ ∈ Γ -> σ ∈ Δ ▻▻ Γ
wkᵛ  vz    = vz
wkᵛ (vs v) = vs (wkᵛ v)

wk : ∀ {n m σ} {Γ : Con n} {Δ : Con m} -> Γ ⊢ σ -> Δ ▻▻ Γ ⊢ σ
wk (var v) = var (wkᵛ v)
wk (ƛ b  ) = ƛ (wk b)
wk (f · x) = wk f · wk x

lift : ∀ {σ} -> Term⁽⁾ σ -> Term⁺ σ
lift t = wk t

⇒-inj : ∀ {σ₁ σ₂ τ₁ τ₂} -> σ₁ ⇒ τ₁ ≡ σ₂ ⇒ τ₂ -> σ₁ ≡ σ₂ × τ₁ ≡ τ₂
⇒-inj refl = refl , refl

_≟ᵗ_ : (σ τ : Type) -> Maybe (σ ≡ τ)
⋆       ≟ᵗ ⋆       = just refl
σ₁ ⇒ τ₁ ≟ᵗ σ₂ ⇒ τ₂ = cong₂ _⇒_ <$> (σ₁ ≟ᵗ σ₂) ⊛ (τ₁ ≟ᵗ τ₂)
_       ≟ᵗ _       = nothing

Env : ℕ -> Set
Env = Vec (∃ Term⁺)

coerce : ∀ {n σ τ} {Γ : Con n} -> Γ ⊢ σ -> Maybe (Γ ⊢ τ)
coerce {σ = σ} {τ} t = (λ p -> subst (_ ⊢_) p t) <$> σ ≟ᵗ τ

lookupᶜ : ∀ {n} -> Fin n -> Con n -> Type
lookupᶜ  fzero   (Γ ▻ σ) = σ
lookupᶜ (fsuc v) (Γ ▻ σ) = lookupᶜ v Γ

lookup-∈ : ∀ {n Γ} -> (v : Fin n) -> lookupᶜ v Γ ∈ Γ
lookup-∈ {Γ = Γ ▻ σ}  fzero   = vz
lookup-∈ {Γ = Γ ▻ σ} (fsuc v) = vs (lookup-∈ v)

mutual
  infer : ∀ {m n} {Γ : Con n} -> Env m -> Syntax m n -> Maybe (∃ (Γ ⊢_))
  infer ρ (free v) = just (proj₁ (lookup v ρ) , proj₂ (lookup v ρ))
  infer ρ (var v ) = just (, var (lookup-∈ v))
  infer ρ (ƛ b   ) = nothing
  infer ρ (f · x ) = infer ρ f >>= λ
    { (σ ⇒ τ , fₜ) -> (λ xₜ -> , fₜ · xₜ) <$> check ρ x σ
    ;  _           -> nothing
    }

  check : ∀ {m n} {Γ : Con n} -> Env m -> Syntax m n -> (σ : Type) -> Maybe (Γ ⊢ σ)
  check ρ (ƛ t) (σ ⇒ τ) = ƛ_ <$> check ρ t τ
  check ρ  t     σ      = infer ρ t >>= coerce ∘ proj₂

data Code m : Set where
  _∋_  : Type -> Syntax⁽⁾ m -> Code m
  _>>_ : Code m -> Code (suc m) -> Code m

Code⁽⁾ : Set
Code⁽⁾ = Code 0

typecheck : ∀ {m} -> Env m -> Code m -> Maybe (∃ Term⁺)
typecheck ρ (σ ∋ t)  = ,_ ∘ lift <$> check ρ t σ
typecheck ρ (c >> d) = typecheck ρ c >>= λ p -> typecheck (p ∷ ρ) d

typecheck⁽⁾ : Code⁽⁾ -> Maybe (∃ Term⁺)
typecheck⁽⁾ = typecheck []

AI : Code⁽⁾
AI =   ⋆ ⇒ ⋆          ∋ ƛ var fzero
   >> (⋆ ⇒ ⋆) ⇒ ⋆ ⇒ ⋆ ∋ ƛ ƛ var (fsuc fzero) · var fzero
   >>           ⋆ ⇒ ⋆ ∋ free fzero · free (fsuc fzero)

test : T ∘ is-just $ typecheck⁽⁾ AI
test = tt
