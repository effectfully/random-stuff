open import Function
open import Data.Nat.Base
open import Data.Sum
open import Data.Product

infixl 5 _▻_
infixr 6 _⇒_
infix  4 _⊑_ _∈_ _⊢_ _⊢ⁿᵉ_ _⊢ⁿᶠ_ _⊨_ _⊨*_
infix  6 vs_
infixr 5 ƛ_ ƛⁿᶠ_
infixl 7 _·_ _·ⁿᵉ_

data Type : Set where
  nat : Type
  _⊛_ : Type -> Type -> Type
  _⇒_ : Type -> Type -> Type

data Con : Set where
  ε   : Con
  _▻_ : Con -> Type -> Con

data _⊑_ : Con -> Con -> Set where
  stop : ε ⊑ ε
  skip : ∀ {Γ Δ τ} -> Γ ⊑ Δ -> Γ     ⊑ Δ ▻ τ
  keep : ∀ {Γ Δ σ} -> Γ ⊑ Δ -> Γ ▻ σ ⊑ Δ ▻ σ

Links : Set -> Set₁
Links A = Con -> A -> Set

_∸>_ : ∀ {A} -> Links A -> Links A -> Set
_∙_ ∸> _◆_ = ∀ {x Γ} -> Γ ∙ x -> Γ ◆ x

Renames : ∀ {A} -> Links A -> Set
Renames _∙_ = ∀ {x Γ Δ} -> Γ ⊑ Δ -> Γ ∙ x -> Δ ∙ x

data _∈_ σ : Con -> Set where
  vz  : ∀ {Γ}   -> σ ∈ Γ ▻ σ
  vs_ : ∀ {Γ τ} -> σ ∈ Γ     -> σ ∈ Γ ▻ τ 

data _⊢_ Γ : Type -> Set where
  var  : ∀ {σ}   -> σ ∈ Γ     -> Γ ⊢ σ
  ƛ_   : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _·_  : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ
  pair : ∀ {σ τ} -> Γ ⊢ σ     -> Γ ⊢ τ     -> Γ ⊢ σ ⊛ τ
  fst  : ∀ {σ τ} -> Γ ⊢ σ ⊛ τ -> Γ ⊢ σ
  snd  : ∀ {σ τ} -> Γ ⊢ σ ⊛ τ -> Γ ⊢ τ
  ze   :            Γ ⊢ nat
  su   :            Γ ⊢ nat   -> Γ ⊢ nat
  iter : ∀ {σ}   -> Γ ⊢ σ ⇒ σ -> Γ ⊢ σ     -> Γ ⊢ nat    -> Γ ⊢ σ

mutual
  data _⊢ⁿᵉ_ Γ : Type -> Set where
    varⁿᵉ  : ∀ {σ}   -> σ ∈ Γ       -> Γ ⊢ⁿᵉ σ
    _·ⁿᵉ_  : ∀ {σ τ} -> Γ ⊢ⁿᵉ σ ⇒ τ -> Γ ⊢ⁿᶠ σ -> Γ ⊢ⁿᵉ τ
    fstⁿᵉ  : ∀ {σ τ} -> Γ ⊢ⁿᵉ σ ⊛ τ -> Γ ⊢ⁿᵉ σ
    sndⁿᵉ  : ∀ {σ τ} -> Γ ⊢ⁿᵉ σ ⊛ τ -> Γ ⊢ⁿᵉ τ
    iterⁿᵉ : ∀ {σ}   -> Γ ⊢ⁿᶠ σ ⇒ σ -> Γ ⊢ⁿᶠ σ -> Γ ⊢ⁿᵉ nat -> Γ ⊢ⁿᵉ σ

  data _⊢ⁿᶠ_ Γ : Type -> Set where
    neⁿᶠ   : ∀ {σ}   -> Γ ⊢ⁿᵉ σ     -> Γ ⊢ⁿᶠ σ
    ƛⁿᶠ_   : ∀ {σ τ} -> Γ ▻ σ ⊢ⁿᶠ τ -> Γ ⊢ⁿᶠ σ ⇒ τ
    pairⁿᶠ : ∀ {σ τ} -> Γ ⊢ⁿᶠ σ     -> Γ ⊢ⁿᶠ τ     -> Γ ⊢ⁿᶠ σ ⊛ τ
    zeⁿᶠ   :            Γ ⊢ⁿᶠ nat
    suⁿᶠ   :            Γ ⊢ⁿᶠ nat   -> Γ ⊢ⁿᶠ nat

full : ∀ {Γ} -> Γ ⊑ Γ
full {ε}     = stop
full {Γ ▻ σ} = keep full

top : ∀ {Γ σ} -> Γ ⊑ Γ ▻ σ
top = skip full

mutual
  embⁿᵉ : _⊢ⁿᵉ_ ∸> _⊢_
  embⁿᵉ (varⁿᵉ v)      = var v
  embⁿᵉ (f ·ⁿᵉ x)      = embⁿᵉ f · embⁿᶠ x
  embⁿᵉ (fstⁿᵉ p)      = fst (embⁿᵉ p)
  embⁿᵉ (sndⁿᵉ p)      = snd (embⁿᵉ p)
  embⁿᵉ (iterⁿᵉ f x n) = iter (embⁿᶠ f) (embⁿᶠ x) (embⁿᵉ n)

  embⁿᶠ : _⊢ⁿᶠ_ ∸> _⊢_
  embⁿᶠ (neⁿᶠ n)     = embⁿᵉ n
  embⁿᶠ (ƛⁿᶠ b)      = ƛ (embⁿᶠ b)
  embⁿᶠ (pairⁿᶠ t u) = pair (embⁿᶠ t) (embⁿᶠ u)
  embⁿᶠ  zeⁿᶠ        = ze
  embⁿᶠ (suⁿᶠ n)     = su (embⁿᶠ n)

mutual
  _⊨_ : Links Type
  Γ ⊨ nat   = Γ ⊢ⁿᶠ nat
  Γ ⊨ σ ⊛ τ = Γ ⊨ σ × Γ ⊨ τ
  Γ ⊨ σ ⇒ τ = ∀ {Δ} -> Γ ⊑ Δ -> Δ ⊨ σ -> Δ ⊨ τ

_∘ˢ_ : Renames (flip _⊑_)
stop   ∘ˢ ι      = ι
skip κ ∘ˢ ι      = skip (κ ∘ˢ ι)
keep κ ∘ˢ skip ι = skip (κ ∘ˢ ι)
keep κ ∘ˢ keep ι = keep (κ ∘ˢ ι)

renᵛ : Renames (flip _∈_)
renᵛ  stop     v     = v
renᵛ (skip ι)  v     = vs (renᵛ ι v)
renᵛ (keep ι)  vz    = vz
renᵛ (keep ι) (vs v) = vs (renᵛ ι v)

mutual
  renⁿᵉ : Renames _⊢ⁿᵉ_
  renⁿᵉ ι (varⁿᵉ v)      = varⁿᵉ (renᵛ ι v)
  renⁿᵉ ι (f ·ⁿᵉ x)      = renⁿᵉ ι f ·ⁿᵉ renⁿᶠ ι x
  renⁿᵉ ι (fstⁿᵉ p)      = fstⁿᵉ (renⁿᵉ ι p)
  renⁿᵉ ι (sndⁿᵉ p)      = sndⁿᵉ (renⁿᵉ ι p)
  renⁿᵉ ι (iterⁿᵉ f x n) = iterⁿᵉ (renⁿᶠ ι f) (renⁿᶠ ι x) (renⁿᵉ ι n)

  renⁿᶠ : Renames _⊢ⁿᶠ_
  renⁿᶠ ι (neⁿᶠ n)     = neⁿᶠ (renⁿᵉ ι n)
  renⁿᶠ ι (ƛⁿᶠ b)      = ƛⁿᶠ (renⁿᶠ (keep ι) b)
  renⁿᶠ ι (pairⁿᶠ t u) = pairⁿᶠ (renⁿᶠ ι t) (renⁿᶠ ι u)
  renⁿᶠ ι  zeⁿᶠ        = zeⁿᶠ
  renⁿᶠ ι (suⁿᶠ n)     = suⁿᶠ (renⁿᶠ ι n)

renᵐ : Renames _⊨_
renᵐ {nat}   ι  n      = renⁿᶠ ι n
renᵐ {σ ⊛ τ} ι (x , y) = renᵐ ι x , renᵐ ι y
renᵐ {σ ⇒ τ} ι  k      = λ κ -> k (κ ∘ˢ ι)

mutual
  reflect : _⊢ⁿᵉ_ ∸> _⊨_
  reflect {nat}   n = neⁿᶠ n
  reflect {σ ⊛ τ} p = reflect (fstⁿᵉ p) , reflect (sndⁿᵉ p)
  reflect {σ ⇒ τ} f = λ ι x -> reflect (renⁿᵉ ι f ·ⁿᵉ reify x)

  varᵐ : flip _∈_ ∸> _⊨_
  varᵐ = reflect ∘ varⁿᵉ

  reify : _⊨_ ∸> _⊢ⁿᶠ_
  reify {nat}    n      = n
  reify {σ ⊛ τ} (x , y) = pairⁿᶠ (reify x) (reify y)
  reify {σ ⇒ τ}  k      = ƛⁿᶠ reify (k top (varᵐ vz)) 

data _⊨*_ Δ : Con -> Set where
  ø   : Δ ⊨* ε
  _▷_ : ∀ {Γ σ} -> Δ ⊨* Γ -> Δ ⊨ σ -> Δ ⊨* Γ ▻ σ

lookupᵉ : ∀ {Γ Δ σ} -> σ ∈ Γ -> Δ ⊨* Γ -> Δ ⊨ σ
lookupᵉ  vz    (ρ ▷ x) = x
lookupᵉ (vs v) (ρ ▷ x) = lookupᵉ v ρ

renᵉ : Renames _⊨*_
renᵉ ι  ø      = ø
renᵉ ι (ρ ▷ x) = renᵉ ι ρ ▷ renᵐ ι x

idᵉ : ∀ {Γ} -> Γ ⊨* Γ
idᵉ {ε}     = ø
idᵉ {Γ ▻ σ} = renᵉ top idᵉ ▷ varᵐ vz

_·ᵐ_ : ∀ {Γ σ τ} -> Γ ⊨ σ ⇒ τ -> Γ ⊨ σ -> Γ ⊨ τ
f ·ᵐ x = f full x

iterᵐ : ∀ {Γ σ} -> Γ ⊨ σ ⇒ σ -> Γ ⊨ σ -> Γ ⊢ⁿᶠ nat -> Γ ⊨ σ
iterᵐ f x (neⁿᶠ n) = reflect (iterⁿᵉ (reify {_ ⇒ _} f) (reify x) n)
iterᵐ f x  zeⁿᶠ    = x
iterᵐ f x (suⁿᶠ n) = f ·ᵐ iterᵐ f x n

⟦_⟧ : ∀ {Γ Δ σ} -> Γ ⊢ σ -> Δ ⊨* Γ -> Δ ⊨ σ
⟦ var v      ⟧ ψ = lookupᵉ v ψ
⟦ ƛ b        ⟧ ψ = λ ι x -> ⟦ b ⟧ (renᵉ ι ψ ▷ x)
⟦ f · x      ⟧ ψ = ⟦ f ⟧ ψ ·ᵐ ⟦ x ⟧ ψ
⟦ pair t u   ⟧ ψ = ⟦ t ⟧ ψ , ⟦ u ⟧ ψ
⟦ fst p      ⟧ ψ = proj₁ (⟦ p ⟧ ψ)
⟦ snd p      ⟧ ψ = proj₂ (⟦ p ⟧ ψ)
⟦ ze         ⟧ ψ = zeⁿᶠ
⟦ su n       ⟧ ψ = suⁿᶠ (⟦ n ⟧ ψ)
⟦ iter f x n ⟧ ψ = iterᵐ (⟦ f ⟧ ψ) (⟦ x ⟧ ψ) (⟦ n ⟧ ψ)

eval : _⊢_ ∸> _⊨_
eval t = ⟦ t ⟧ idᵉ

norm : _⊢_ ∸> _⊢_
norm = embⁿᶠ ∘ reify ∘ eval
