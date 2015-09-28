module SC.Basic where

open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty
open import Data.Sum     renaming (map to smap)
open import Data.Product renaming (map to pmap)

infixr 5 _⇒_
infixl 6 _▻_ _▻ʳ_
infix  3 _≈_▻ʳ_ _∈_ _∈ʳ_ _∉ʳ_ _⊆_ _⊆²_ _[_⊢_]
infixr 5 vs_
infixr 4 ƛ_ fix_
infixl 7 _·_

data Type : Set where
  _⇒_  : Type -> Type -> Type
  nat  : Type
  list : Type -> Type

data Con : Set where
  ε   : Con
  _▻_ : Con -> Type -> Con

data _∈_ σ : Con -> Set where
  vz  : ∀ {Γ}   -> σ ∈ Γ ▻ σ
  vs_ : ∀ {Γ τ} -> σ ∈ Γ     -> σ ∈ Γ ▻ τ

data _≈_▻ʳ_ : Con -> Con -> Type -> Set where
  ▻ʳ-base : ∀ {σ}       -> ε ▻ σ ≈ ε ▻ʳ σ
  ▻ʳ-step : ∀ {Γ Δ σ τ} -> Δ ≈ Γ ▻ʳ σ     -> Δ ▻ τ ≈ (Γ ▻ τ) ▻ʳ σ

data _∈ʳ_ σ : Con -> Set where
  vzʳ : ∀ {Γ Δ}   -> Δ ≈ Γ ▻ʳ σ -> σ ∈ʳ Δ
  vsʳ : ∀ {Γ Δ τ} -> Δ ≈ Γ ▻ʳ τ -> σ ∈ʳ Γ -> σ ∈ʳ Δ

data _⊆_ : Con -> Con -> Set where
  stop : ∀ {Γ}     -> Γ ⊆ Γ
  skip : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ     ⊆ Δ ▻ σ
  keep : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ▻ σ ⊆ Δ ▻ σ

data _⊆²_ : Con × Con -> Con × Con -> Set where
  stop : ∀ {Γ Δ}           -> Γ  , Δ  ⊆² Γ  , Δ
  skip : ∀ {Γ₀ Γ₁ Δ₀ Δ₁ σ} -> Γ₀ , Δ₀ ⊆² Γ₁ , Δ₁ -> Γ₀     , Δ₀ ⊆² Γ₁ ▻ σ , Δ₁ ▻ σ
  keep : ∀ {Γ₀ Γ₁ Δ₀ Δ₁ σ} -> Γ₀ , Δ₀ ⊆² Γ₁ , Δ₁ -> Γ₀ ▻ σ , Δ₀ ⊆² Γ₁ ▻ σ , Δ₁

data _[_⊢_] Δ Γ : Type -> Set where
  bvar : ∀ {σ}   -> σ ∈  Γ          -> Δ [ Γ ⊢ σ ]
  fvar : ∀ {σ}   -> σ ∈ʳ Δ          -> Δ [ Γ ⊢ σ ]
  ƛ_   : ∀ {σ τ} -> Δ [ Γ ▻ σ ⊢ τ ] -> Δ [ Γ ⊢ σ ⇒ τ ]
  _·_  : ∀ {σ τ} -> Δ [ Γ ⊢ σ ⇒ τ ] -> Δ [ Γ ⊢ σ ]     -> Δ [ Γ ⊢ τ ]
  fix_ : ∀ {σ}   -> Δ [ Γ ⊢ σ ⇒ σ ] -> Δ [ Γ ⊢ σ ]

_∉ʳ_ : Type -> Con -> Set
σ ∉ʳ Γ = σ ∈ʳ Γ -> ⊥

_▻ʳ_ : Con -> Type -> Con
ε     ▻ʳ σ = ε ▻ σ
Γ ▻ τ ▻ʳ σ = Γ ▻ʳ σ ▻ τ

▻ʳ-≈-▻ʳ : ∀ {Γ σ} -> Γ ▻ʳ σ ≈ Γ ▻ʳ σ
▻ʳ-≈-▻ʳ {ε}     = ▻ʳ-base
▻ʳ-≈-▻ʳ {Γ ▻ τ} = ▻ʳ-step ▻ʳ-≈-▻ʳ

to-≈-▻ʳ : ∀ {Γ Δ σ} -> Δ ≡ Γ ▻ʳ σ -> Δ ≈ Γ ▻ʳ σ
to-≈-▻ʳ refl = ▻ʳ-≈-▻ʳ

from-≈-▻ʳ : ∀ {Γ Δ σ} -> Δ ≈ Γ ▻ʳ σ -> Δ ≡ Γ ▻ʳ σ 
from-≈-▻ʳ  ▻ʳ-base    = refl
from-≈-▻ʳ (▻ʳ-step p) = cong (_▻ _) (from-≈-▻ʳ p)

cong-▻-≈-▻ʳ : ∀ {Γ Δ σ τ} -> Δ ≈ Γ ▻ʳ σ -> Δ ▻ τ ≈ Γ ▻ τ ▻ʳ σ
cong-▻-≈-▻ʳ = to-≈-▻ʳ ∘ cong (_▻ _) ∘ from-≈-▻ʳ

from-⊆² : ∀ {Γ₀ Γ₁ Δ₀ Δ₁} -> Γ₀ , Δ₀ ⊆² Γ₁ , Δ₁ -> Γ₀ ⊆ Γ₁ × Δ₀ ⊆ Δ₁
from-⊆²  stop    = stop , stop
from-⊆² (skip ι) = pmap skip skip (from-⊆² ι)
from-⊆² (keep ι) = pmap keep id   (from-⊆² ι)

∉ʳ-ε : ∀ {σ} -> σ ∉ʳ ε
∉ʳ-ε (vzʳ ())
∉ʳ-ε (vsʳ () v)

matchᵛʳ : ∀ {Γ σ τ} -> σ ∈ʳ Γ ▻ τ -> σ ≡ τ ⊎ σ ∈ʳ Γ
matchᵛʳ (vzʳ  ▻ʳ-base)      = inj₁ refl
matchᵛʳ (vzʳ (▻ʳ-step p))   = inj₂ (vzʳ p)
matchᵛʳ (vsʳ  ▻ʳ-base    v) = ⊥-elim (∉ʳ-ε v)
matchᵛʳ (vsʳ (▻ʳ-step p) v) = smap id (vsʳ p) (matchᵛʳ v)

wkʳ : ∀ {Γ σ τ} -> σ ∈ʳ Γ -> σ ∈ʳ Γ ▻ τ
wkʳ (vzʳ p)   = vzʳ (cong-▻-≈-▻ʳ p)
wkʳ (vsʳ p v) = vsʳ (cong-▻-≈-▻ʳ p) (wkʳ v)

insʳ : ∀ {Γ σ τ ν} -> σ ∈ʳ Γ ▻ τ -> σ ∈ʳ Γ ▻ ν ▻ τ
insʳ (vzʳ  ▻ʳ-base)      = vsʳ (▻ʳ-step ▻ʳ-base) (vzʳ ▻ʳ-base)
insʳ (vzʳ (▻ʳ-step p))   = vzʳ (▻ʳ-step (▻ʳ-step p))
insʳ (vsʳ  ▻ʳ-base    v) = ⊥-elim (∉ʳ-ε v)
insʳ (vsʳ (▻ʳ-step p) v) = vsʳ (▻ʳ-step (▻ʳ-step p)) (insʳ v)

fullʳ : ∀ {Γ σ} -> σ ∈ʳ Γ ▻ σ
fullʳ {ε}     = vzʳ ▻ʳ-base
fullʳ {Γ ▻ τ} = insʳ fullʳ

to-∈ : ∀ {Γ σ} -> σ ∈ʳ Γ -> σ ∈ Γ
to-∈ {ε}     v = ⊥-elim (∉ʳ-ε v)
to-∈ {Γ ▻ τ} v with matchᵛʳ v
... | inj₁ p rewrite p = vz
... | inj₂ w = vs (to-∈ w)

to-∈ʳ : ∀ {Γ σ} -> σ ∈ Γ -> σ ∈ʳ Γ
to-∈ʳ  vz    = fullʳ
to-∈ʳ (vs v) = wkʳ (to-∈ʳ v)

weakenᵛ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> σ ∈ Γ -> σ ∈ Δ
weakenᵛ  stop     v     = v
weakenᵛ (skip ι)  v     = vs (weakenᵛ ι v)
weakenᵛ (keep ι)  vz    = vz
weakenᵛ (keep ι) (vs v) = vs (weakenᵛ ι v)

weakenᵛʳ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> σ ∈ʳ Γ -> σ ∈ʳ Δ
weakenᵛʳ  stop    v = v
weakenᵛʳ (skip ι) v = wkʳ (weakenᵛʳ ι v)
weakenᵛʳ (keep ι) v with matchᵛʳ v 
... | inj₁ p rewrite p = fullʳ
... | inj₂ w = wkʳ (weakenᵛʳ ι w)

closeᵛ : ∀ {Γ₀ Γ₁ Δ₀ Δ₁ σ} -> Γ₀ , Δ₀ ⊆² Γ₁ , Δ₁ -> σ ∈ʳ Δ₁ -> σ ∈ Γ₁ ⊎ σ ∈ʳ Δ₀
closeᵛ  stop    v = inj₂ v
closeᵛ (skip ι) v with matchᵛʳ v
... | inj₁ p rewrite p = inj₁ vz
... | inj₂ w = smap vs_ id (closeᵛ ι w)
closeᵛ (keep ι) v = smap vs_ id (closeᵛ ι v)

openᵛ : ∀ {Γ₀ Γ₁ Δ₀ Δ₁ σ} -> Γ₀ , Δ₀ ⊆² Γ₁ , Δ₁ -> σ ∈ Γ₁ -> σ ∈ʳ Δ₁ ⊎ σ ∈ Γ₀
openᵛ  stop     v     = inj₂ v
openᵛ (skip ι)  vz    = inj₁ fullʳ
openᵛ (skip ι) (vs v) = smap wkʳ id (openᵛ ι v)
openᵛ (keep ι)  vz    = inj₂ vz
openᵛ (keep ι) (vs v) = smap id vs_ (openᵛ ι v)

closeᵗ : ∀ {Γ₀ Γ₁ Δ₀ Δ₁ σ} -> Γ₀ , Δ₀ ⊆² Γ₁ , Δ₁ -> Δ₁ [ Γ₀ ⊢ σ ] -> Δ₀ [ Γ₁ ⊢ σ ]
closeᵗ ι (bvar v) = bvar (weakenᵛ (proj₁ (from-⊆² ι)) v)
closeᵗ ι (fvar v) = [ bvar , fvar ]′ (closeᵛ ι v)
closeᵗ ι (ƛ b)    = ƛ (closeᵗ (keep ι) b)
closeᵗ ι (f · x)  = closeᵗ ι f · closeᵗ ι x
closeᵗ ι (fix b)  = fix (closeᵗ ι b)

openᵗ : ∀ {Γ₀ Γ₁ Δ₀ Δ₁ σ} -> Γ₀ , Δ₀ ⊆² Γ₁ , Δ₁ -> Δ₀ [ Γ₁ ⊢ σ ] -> Δ₁ [ Γ₀ ⊢ σ ]
openᵗ ι (bvar v) = [ fvar , bvar ]′ (openᵛ ι v)
openᵗ ι (fvar v) = fvar (weakenᵛʳ (proj₂ (from-⊆² ι)) v)
openᵗ ι (ƛ b)    = ƛ (openᵗ (keep ι) b)
openᵗ ι (f · x)  = openᵗ ι f · openᵗ ι x
openᵗ ι (fix b)  = fix (openᵗ ι b)
