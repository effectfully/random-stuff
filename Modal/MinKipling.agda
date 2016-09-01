{-# OPTIONS --no-positivity-check --no-termination-check --rewriting #-}

open import Function hiding (_∋_)
open import Relation.Binary.PropositionalEquality hiding (subst)
open import Data.Unit.Base
open import Data.Nat.Base
open import Data.Product renaming (uncurry to ᵛ; curry to ̂)

{-# BUILTIN REWRITE _≡_ #-}

infixr 5 ᵏ_
ᵏ_ = const

infix  4 _⊢_ _⊢*_
infixr 6 _⇒_
infixl 5 _▻_
infixr 7 ƛ_
infixr 9 vs_
infixl 8 _·_

elimℕ : ∀ {π} -> (P : ℕ -> Set π) -> (∀ n -> P n -> P (suc n)) -> P 0 -> ∀ n -> P n
elimℕ P f z  0      = z
elimℕ P f z (suc n) = f n (elimℕ P f z n)

data U : Set
Term : U -> Set

data U where
  nat  : U
  π    : ∀ A -> (Term A -> U) -> U
  susp : U -> U
  term : U -> U

⟦_⟧ᵘ : U -> Set
⟦ nat    ⟧ᵘ = ℕ
⟦ π A B  ⟧ᵘ = ∀ x -> ⟦ B x ⟧ᵘ
⟦ susp A ⟧ᵘ = ⟦ A ⟧ᵘ
⟦ term A ⟧ᵘ = Term A

_⇒_ : U -> U -> U
A ⇒ B = π A λ _ -> B

mutual
  data Con : Set where
    ε   : Con
    _▻_ : ∀ Γ -> IU Γ -> Con

  IU : Con -> Set
  IU Γ = ⟦ Γ ⟧ᶜ -> U

  ⟦_⟧ᶜ : Con -> Set
  ⟦ ε     ⟧ᶜ = ⊤
  ⟦ Γ ▻ A ⟧ᶜ = ∃ λ γ -> Term (A γ)

data _⊢_ : ∀ Γ -> IU Γ -> Set
fillIn : ∀ {Γ A} -> Γ ⊢ A -> ∀ γ -> Term (A γ)

mutual
  data _⊢*_ : Con -> Con -> Set where
    ø   : ∀ {Δ} -> Δ ⊢* ε
    _▷_ : ∀ {Γ Δ A} -> (ψ : Δ ⊢* Γ) -> Δ ⊢ A ∘ fill* ψ -> Δ ⊢* Γ ▻ A
    ext : ∀ {Γ Δ A} -> (ψ : Δ ⊢* Γ) -> Δ ▻ A ∘ fill* ψ ⊢* Γ ▻ A

  fill* : ∀ {Γ Δ} -> Δ ⊢* Γ -> ⟦ Δ ⟧ᶜ -> ⟦ Γ ⟧ᶜ
  fill*  ø       δ      = tt
  fill* (ψ ▷ t)  δ      = fill* ψ δ , fillIn t δ
  fill* (ext ψ) (δ , t) = fill* ψ δ , t

Term A = ε ⊢ ᵏ A

eval  : ∀ {A} -> Term A -> ⟦ A ⟧ᵘ
normn : Term nat -> Term nat

data _⊢_ where
  vz    : ∀ {Γ A} -> Γ ▻ A ⊢ A ∘ proj₁
  vs_   : ∀ {Γ A B} -> Γ ⊢ A -> Γ ▻ B ⊢ A ∘ proj₁
  ƛ_    : ∀ {Γ A B} -> Γ ▻ A ⊢ ᵛ B -> Γ ⊢ π ∘ A ˢ B
  _·_   : ∀ {Γ A B} -> Γ ⊢ π ∘ A ˢ B -> (x : Γ ⊢ A) -> Γ ⊢ B ˢ fillIn x
  embn  : ∀ {Γ} -> ℕ -> Γ ⊢ ᵏ nat
  su    : ∀ {Γ} -> Γ ⊢ ᵏ nat ⇒ nat
  elimn : ∀ {Γ}
        -> (P : ⟦ Γ ⟧ᶜ -> Term nat -> U)
        -> Γ ⊢ λ γ -> (π nat λ n -> P γ (normn n) ⇒ P γ (normn (su · n)))
                    ⇒ P γ (embn 0) ⇒ π nat λ n -> P γ (normn n)
  ret   : ∀ {Γ A}   -> Γ ⊢ ᵏ A ⇒ susp A
  bind  : ∀ {Γ A B} -> Γ ⊢ ᵏ susp A ⇒ (A ⇒ susp B) ⇒ susp B
  quot  : ∀ {Γ A} -> Γ ⊢ A -> Γ ⊢ susp ∘ term ∘ A
  exec  : ∀ {Γ A} -> Term (susp A) -> Γ ⊢ ᵏ A
  lift  : ∀ {Γ A B} -> (∀ γ -> Term A -> ⟦ B γ ⟧ᵘ) -> Γ ⊢ _⇒_ (term A) ∘ B

subst : ∀ {Γ Δ A} ψ -> Γ ⊢ A -> Δ ⊢ A ∘ fill* ψ

postulate
  fillIn-fill* : ∀ {Γ Δ A} {ψ : Δ ⊢* Γ} {δ : ⟦ Δ ⟧ᶜ} {t : Γ ⊢ A}
               -> fillIn t (fill* ψ δ) ≡ fillIn (subst ψ t) δ

{-# REWRITE fillIn-fill* #-}

subst (ψ ▷ x)  vz       = x
subst (ext ψ)  vz       = vz
subst (ψ ▷ x) (vs t)    = subst ψ t
subst (ext ψ) (vs t)    = vs (subst ψ t)
subst  ψ      (ƛ b)     = ƛ subst (ext ψ) b
subst  ψ      (f · x)   = subst ψ f · subst ψ x
subst  ψ      (embn n)  = embn n
subst  ψ       su       = su
subst  ψ       ret      = ret
subst  ψ       bind     = bind
subst  ψ      (elimn P) = elimn (P ∘ fill* ψ)
subst  ψ      (quot t)  = quot (subst ψ t)
subst  ψ      (exec t)  = exec t
subst  ψ      (lift f)  = lift (f ∘ fill* ψ)

reifyEnv : ∀ {Γ} -> ⟦ Γ ⟧ᶜ -> ε ⊢* Γ

postulate
  fill*-reifyEnv : ∀ {Γ} -> (γ : ⟦ Γ ⟧ᶜ) -> fill* (reifyEnv γ) tt ≡ γ

{-# REWRITE fill*-reifyEnv #-}

reifyEnv {ε}      tt     = ø
reifyEnv {Γ ▻ A} (γ , t) = reifyEnv γ ▷ t

fillIn {ε} = ᵏ_
fillIn     = flip (subst ∘ reifyEnv)

⟦_⟧ : ∀ {Γ A} -> Γ ⊢ A -> ∀ γ -> ⟦ A γ ⟧ᵘ

eval t = ⟦ t ⟧ tt
normn  = embn ∘ eval

⟦ vz      ⟧ = eval ∘ proj₂
⟦ vs t    ⟧ = ⟦ t ⟧ ∘ proj₁
⟦ ƛ b     ⟧ = ̂ ⟦ b ⟧
⟦ f · x   ⟧ = ⟦ f ⟧ ˢ fillIn x
⟦ embn n  ⟧ = ᵏ n
⟦ su      ⟧ = ᵏ suc ∘ eval
⟦ elimn P ⟧ = λ γ f x -> eval ∘ elimℕ (Term ∘ P γ ∘ embn) (λ n r -> f · embn n · r) x ∘ eval
⟦ ret     ⟧ = ᵏ eval
⟦ bind    ⟧ = ᵏ λ x f -> eval f (exec x)
⟦ quot t  ⟧ = fillIn t
⟦ exec t  ⟧ = ᵏ eval t
⟦ lift f  ⟧ = _∘′_ ∘ f ˢ (ᵏ eval)

wk : ∀ {Γ A} -> Term A -> Γ ⊢ ᵏ A
wk = subst ø

assemble : ∀ {Γ A} -> Γ ⊢ ᵏ term A ⇒ A
assemble = lift (ᵏ eval)

Term⁺ : U -> Set
Term⁺ A = ∀ {Γ} -> Γ ⊢ ᵏ A

fmap : ∀ {Γ A B} -> Γ ⊢ ᵏ (A ⇒ B) ⇒ susp A ⇒ susp B
fmap = ƛ ƛ bind · vz · (ƛ ret · (vs vs vz · vz))

metaCountVars : ∀ {Γ A} -> Γ ⊢ A -> ℕ
metaCountVars  vz      = 1
metaCountVars (vs t)   = metaCountVars t
metaCountVars (ƛ b)    = metaCountVars b
metaCountVars (f · x)  = metaCountVars f + metaCountVars x
metaCountVars (quot t) = metaCountVars t
metaCountVars (exec t) = metaCountVars t
metaCountVars  _       = 0

countVars : ∀ {A} -> Term⁺ (A ⇒ susp nat)
countVars = ƛ fmap · lift (ᵏ metaCountVars) · quot vz

pureMetaCountVars : ∀ {A} -> Term A -> Term nat
pureMetaCountVars t = exec (countVars · t)

runCountVars : ∀ {A} -> Term A -> ℕ
runCountVars = eval ∘ pureMetaCountVars

Iᵗ : ∀ {A} -> Term⁺ (A ⇒ A)
Iᵗ = ƛ vz

Aᵗ : ∀ {A B} -> Term⁺ (π A B ⇒ π A B)
Aᵗ = ƛ ƛ vs vz · vz

Sᵗ : ∀ {A B} {C : ∀ x -> Term (B x) -> U}
   -> Term⁺ (π A (π ∘ B ˢ C) ⇒ π (π A B) λ f -> π A λ x -> C x (f · x))
Sᵗ = ƛ ƛ ƛ vs vs vz · vz · (vs vz · vz)

testI : ∀ {A} -> runCountVars (Iᵗ {A}) ≡ 1
testI = refl

testA : ∀ {A B} -> runCountVars (Aᵗ {A} {B}) ≡ 2
testA = refl

testS : ∀ {A B C} -> runCountVars (Sᵗ {A} {B} {C}) ≡ 4
testS = refl

countVarsCountVars : Term⁺ nat
countVarsCountVars = exec $ countVars · countVars {nat}

-- `quot` is applied to 1 variable and `fmap` contains `3`, hence 4.
testCountVars : eval countVarsCountVars ≡ 4
testCountVars = refl
