open import Function
open import Data.Nat.Base as Nat hiding (fold)

infixl 5 _▻_ _▷_
infixr 6 _⇒_
infix  4 _∈_ _⊢_ _⊑_ _⊢*_
infix  4 vs_
infixr 3 ƛ_
infixl 6 _·_

data Type : Set where
  _⇒_ : Type -> Type -> Type
  □   : Type -> Type
  q   : Type -> Type
  nat : Type

data Con : Set where
  ε   : Con
  _▻_ : Con -> Type -> Con

data _⊑_ : Con -> Con -> Set where
  stop : ∀ {Γ}     -> Γ ⊑ Γ
  skip : ∀ {Γ Δ τ} -> Γ ⊑ Δ -> Γ     ⊑ Δ ▻ τ
  keep : ∀ {Γ Δ σ} -> Γ ⊑ Δ -> Γ ▻ σ ⊑ Δ ▻ σ

data _∈_ σ : Con -> Set where
  vz  : ∀ {Γ}            -> σ ∈ Γ ▻ σ
  vs_ : ∀ {Γ τ} -> σ ∈ Γ -> σ ∈ Γ ▻ τ 

mutual
  data _⊢_ Γ : Type -> Set where
    var  : ∀ {σ}   -> σ ∈ Γ         -> Γ ⊢ σ
    ƛ_   : ∀ {σ τ} -> Γ ▻ σ ⊢ τ     -> Γ ⊢ σ ⇒ τ
    _·_  : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ     -> Γ ⊢ σ       -> Γ ⊢ τ
    _∙_  : ∀ {σ τ} -> Γ ⊢ □ (σ ⇒ τ) -> Γ ⊢ □ σ     -> Γ ⊢ □ τ
    quot : ∀ {σ}   -> Γ ⊢ σ         -> Γ ⊢ q (□ σ)
    runq : ∀ {σ}   -> Term (q σ)    -> Γ ⊢ σ

    ret  : ∀ {σ}   -> Γ ⊢ σ ⇒ q σ
    bind : ∀ {σ τ} -> Γ ⊢ q σ ⇒ (σ ⇒ q τ) ⇒ q τ
    asse : ∀ {σ}   -> Γ ⊢ □ σ ⇒ σ
    elim : ∀ {σ τ} -> Γ ⊢ (τ ⇒ τ ⇒ τ) ⇒ (nat ⇒ τ) ⇒ τ ⇒ □ σ ⇒ τ
    z    :            Γ ⊢ nat
    s    :            Γ ⊢ nat ⇒ nat
    fold : ∀ {τ}   -> Γ ⊢ (τ ⇒ τ) ⇒ τ ⇒ nat ⇒ τ

  Term : Type -> Set
  Term σ = ε ⊢ σ

data _⊢*_ Δ : Con -> Set where
  ø   : Δ ⊢* ε
  _▷_ : ∀ {Γ σ} -> Δ ⊢* Γ -> Δ ⊢ σ -> Δ ⊢* Γ ▻ σ

Env : Con -> Set
Env Γ = ε ⊢* Γ

fmap : ∀ {Γ σ τ} -> Γ ⊢ (σ ⇒ τ) ⇒ q σ ⇒ q τ
fmap = ƛ ƛ bind · var vz · (ƛ ret · (var (vs vs vz) · var vz))

top : ∀ {Γ σ} -> Γ ⊑ Γ ▻ σ
top = skip stop

∈→ℕ : ∀ {Γ σ} -> σ ∈ Γ -> ℕ
∈→ℕ  vz    = 0
∈→ℕ (vs v) = suc (∈→ℕ v)

renᵛ : ∀ {Γ Δ σ} -> Γ ⊑ Δ -> σ ∈ Γ -> σ ∈ Δ
renᵛ  stop     v     = v
renᵛ (skip ψ)  v     = vs (renᵛ ψ v)
renᵛ (keep ψ)  vz    = vz
renᵛ (keep ψ) (vs v) = vs (renᵛ ψ v)

ren : ∀ {Γ Δ σ} -> Γ ⊑ Δ -> Γ ⊢ σ -> Δ ⊢ σ
ren ι (var v)  = var (renᵛ ι v)
ren ι (ƛ b)    = ƛ ren (keep ι) b
ren ι (f · x)  = ren ι f · ren ι x
ren ι (f ∙ x)  = ren ι f ∙ ren ι x
ren ι (quot t) = quot (ren ι t)
ren ι (runq t) = runq t
ren ι  ret     = ret
ren ι  bind    = bind
ren ι  asse    = asse
ren ι  elim    = elim
ren ι  z       = z
ren ι  s       = s
ren ι  fold    = fold

ren* : ∀ {Γ Δ Ξ} -> Δ ⊑ Ξ -> Δ ⊢* Γ -> Ξ ⊢* Γ
ren* ι  ø      = ø
ren* ι (ψ ▷ t) = ren* ι ψ ▷ ren ι t

lookup : ∀ {Δ Γ σ} -> σ ∈ Γ -> Δ ⊢* Γ -> Δ ⊢ σ
lookup  vz    (ψ ▷ t) = t
lookup (vs v) (ψ ▷ t) = lookup v ψ

keep* : ∀ {Δ Γ σ} -> Δ ⊢* Γ -> Δ ▻ σ ⊢* Γ ▻ σ
keep* ψ = ren* top ψ ▷ var vz

subst : ∀ {Δ Γ σ} -> Δ ⊢* Γ -> Γ ⊢ σ -> Δ ⊢ σ
subst ψ (var v)  = lookup v ψ
subst ψ (ƛ b)    = ƛ (subst (keep* ψ) b)
subst ψ (f · x)  = subst ψ f · subst ψ x
subst ψ (f ∙ x)  = subst ψ f ∙ subst ψ x
subst ψ (quot t) = quot (subst ψ t)
subst ψ (runq t) = runq t
subst ψ  ret     = ret
subst ψ  bind    = bind
subst ψ  asse    = asse
subst ψ  z       = z
subst ψ  s       = s
subst ψ  fold    = fold
subst ψ  elim    = elim

-- A tiny optimization.
fill : ∀ {Γ σ} -> Env Γ -> Γ ⊢ σ -> Term σ
fill ø = id
fill ψ = subst ψ

module _ {A : Set} (g : A -> A -> A) (f : ℕ -> A) (x : A) where
  foldTerm : ∀ {Γ σ} -> Γ ⊢ σ -> A
  foldTerm (var v)  = f (∈→ℕ v)
  foldTerm (ƛ b)    = foldTerm b
  foldTerm (f · x)  = g (foldTerm f) (foldTerm x)
  foldTerm (f ∙ x)  = g (foldTerm f) (foldTerm x)
  foldTerm (quot t) = foldTerm t
  foldTerm (runq t) = foldTerm t
  foldTerm  _       = x

⟦_⟧ᵗ : Type -> Set
⟦ σ ⇒ τ ⟧ᵗ = Term σ -> ⟦ τ ⟧ᵗ
⟦ □ σ   ⟧ᵗ = Term σ
⟦ nat   ⟧ᵗ = ℕ
⟦ q σ   ⟧ᵗ = ⟦ σ ⟧ᵗ

reifyℕ : ℕ -> Term nat
reifyℕ = Nat.fold z (s ·_)

{-# TERMINATING #-} -- I have no idea.
mutual
  ⟦_⟧ : ∀ {Γ σ} -> Γ ⊢ σ -> Env Γ -> ⟦ σ ⟧ᵗ
  ⟦ var v  ⟧ ψ = eval (lookup v ψ)
  ⟦ ƛ b    ⟧ ψ = λ x -> ⟦ b ⟧ (ψ ▷ x)
  ⟦ f · x  ⟧ ψ = ⟦ f ⟧ ψ (fill ψ x)
  ⟦ f ∙ x  ⟧ ψ = ⟦ f ⟧ ψ · ⟦ x ⟧ ψ
  ⟦ quot t ⟧ ψ = fill ψ t
  ⟦ runq t ⟧ ψ = eval t
  ⟦ ret    ⟧ ψ = eval
  ⟦ bind   ⟧ ψ = λ x f -> eval f (runq x)
  ⟦ asse   ⟧ ψ = eval ∘ eval
  ⟦ elim   ⟧ ψ = λ g f x -> eval ∘ foldTerm (λ x y -> g · x · y) (λ n -> f · reifyℕ n) x
  ⟦ z      ⟧ ψ = 0
  ⟦ s      ⟧ ψ = suc ∘ eval
  ⟦ fold   ⟧ ψ = λ f x -> eval ∘ Nat.fold x (f ·_) ∘ eval

  eval : ∀ {σ} -> Term σ -> ⟦ σ ⟧ᵗ
  eval t = ⟦ t ⟧ ø

Term⁺ : Type -> Set
Term⁺ σ = ∀ {Γ} -> Γ ⊢ σ

open import Relation.Binary.PropositionalEquality

I : ∀ {σ} -> Term⁺ (σ ⇒ σ)
I = ƛ var vz

A : ∀ {σ τ} -> Term⁺ ((σ ⇒ τ) ⇒ σ ⇒ τ)
A = ƛ ƛ var (vs vz) · var vz

plus : Term⁺ (nat ⇒ nat ⇒ nat)
plus = ƛ ƛ fold · (ƛ s · var vz) · var vz · var (vs vz)

countVars : ∀ {σ} -> Term⁺ (σ ⇒ q nat)
countVars = ƛ fmap · (elim · plus · (ƛ s · z) · z) · quot (var vz)

pureMetaCountVars : ∀ {σ} -> Term σ -> Term nat
pureMetaCountVars t = runq (countVars · t)

runCountVars : ∀ {σ} -> Term σ -> ℕ
runCountVars = eval ∘ pureMetaCountVars

testI : ∀ {σ} -> runCountVars (I {σ}) ≡ 1
testI = refl

testA : ∀ {σ τ} -> runCountVars (A {σ} {τ}) ≡ 2
testA = refl

testPlus : runCountVars plus ≡ 3
testPlus = refl

countVarsCountVars : Term⁺ nat
countVarsCountVars = runq $ countVars · countVars {nat}

-- `quot` is applied to 1 variable, `fmap` contains `3` and `plus` contains 3, hence 7.
testCountVars : eval countVarsCountVars ≡ 7
testCountVars = refl
