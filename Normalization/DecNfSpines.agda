open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Nat.Base
open import Data.Sum renaming (map to smap)

fromInj₁ : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> A ⊎ B -> B
fromInj₁ f = [ f , id ]′

fromInj₂ : ∀ {α β} {A : Set α} {B : Set β} -> (B -> A) -> A ⊎ B -> A
fromInj₂ g = [ id , g ]′

infixl 6 _▻_
infixr 6 _⇒_
infix  4 _⊢_ _∈_
infixl 7 _·_

data Type : Set where
  ι   : Type
  _⇒_ : Type -> Type -> Type

data Con : Set where
  ε   : Con
  _▻_ : Con -> Type -> Con

data _∈_ σ : Con -> Set where
  vz  : ∀ {Γ}   -> σ ∈ Γ ▻ σ
  vs_ : ∀ {Γ τ} -> σ ∈ Γ     -> σ ∈ Γ ▻ τ 

data _⊢_ Γ : Type -> Set where
  var  : ∀ {σ}   -> σ ∈ Γ     -> Γ ⊢ σ
  ƛ    : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _·_  : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ
  unit : Γ ⊢ ι

mutual
  data Nf {Γ} : ∀ {σ} -> Γ ⊢ σ -> Set where
    neⁿᶠ   : ∀ {σ} {t : Γ ⊢ σ} -> Ne t -> Nf t
    ƛⁿᶠ    : ∀ {σ τ} {b : Γ ▻ σ ⊢ τ} -> Nf b -> Nf (ƛ b)
    unitⁿᶠ : Nf unit

  data Ne {Γ} : ∀ {σ} -> Γ ⊢ σ -> Set where
    spⁿᵉ : ∀ {σ τ} {v : σ ∈ Γ} {t : Γ ⊢ τ} -> Head v t -> Ne t

  data Head {Γ σ} (v : σ ∈ Γ) : ∀ {τ} -> Γ ⊢ τ -> Set where
    ø   : Head v (var v)
    _▷_ : ∀ {τ ν} {t : Γ ⊢ τ ⇒ ν} {s : Γ ⊢ τ} -> Head v t -> Nf s -> Head v (t · s)

Shaped : ∀ {Γ σ} -> Γ ⊢ σ -> Set
Shaped t = Ne t ⊎ Nf t

nfˢ : ∀ {Γ σ} {t : Γ ⊢ σ}
    -> Shaped t -> Nf t
nfˢ = fromInj₁ neⁿᶠ

-- We really need pattern matching pattern synonyms.
_·ⁿᵉ_ : ∀ {Γ σ τ} {f : Γ ⊢ σ ⇒ τ} {x} -> Ne f -> Nf x -> Ne (f · x)
spⁿᵉ f ·ⁿᵉ x = spⁿᵉ (f ▷ x)

appˢ : ∀ {Γ σ τ} {f : Γ ⊢ σ ⇒ τ} {x}
     -> Ne f -> Shaped x -> Shaped (f · x)
appˢ f = inj₁ ∘ _·ⁿᵉ_ f ∘ nfˢ

ƛˢ : ∀ {Γ σ τ} {b : Γ ▻ σ ⊢ τ}
   -> Shaped b -> Shaped (ƛ b)
ƛˢ = inj₂ ∘ ƛⁿᶠ ∘ nfˢ

unappⁿᶠ : ∀ {Γ σ τ} {f : Γ ⊢ σ ⇒ τ} {x}
        -> Nf (f · x) -> Ne (f · x)
unappⁿᶠ (neⁿᶠ t) = t

unfunⁿᵉ : ∀ {Γ σ τ} {f : Γ ⊢ σ ⇒ τ} {x}
        -> Ne (f · x) -> Ne f
unfunⁿᵉ (spⁿᵉ (f ▷ x)) = spⁿᵉ f

unargⁿᵉ : ∀ {Γ σ τ} {f : Γ ⊢ σ ⇒ τ} {x}
        -> Ne (f · x) -> Nf x
unargⁿᵉ (spⁿᵉ (f ▷ x)) = x

unƛⁿᶠ : ∀ {Γ σ τ} {b : Γ ▻ σ ⊢ τ}
      -> Nf (ƛ b) -> Nf b
unƛⁿᶠ (neⁿᶠ (spⁿᵉ ()))
unƛⁿᶠ (ƛⁿᶠ b) = b

noβⁿᵉ : ∀ {Γ σ τ} {b : Γ ▻ σ ⊢ τ} {x}
      -> ¬ Ne (ƛ b · x)
noβⁿᵉ (spⁿᵉ (() ▷ _))

unappˢ : ∀ {Γ σ τ} {f : Γ ⊢ σ ⇒ τ} {x}
       -> Shaped (f · x) -> Ne (f · x)
unappˢ = fromInj₂ unappⁿᶠ

unfunˢ : ∀ {Γ σ τ} {f : Γ ⊢ σ ⇒ τ} {x}
       -> Shaped (f · x) -> Shaped f
unfunˢ = inj₁ ∘ unfunⁿᵉ ∘ unappˢ

unargˢ : ∀ {Γ σ τ} {f : Γ ⊢ σ ⇒ τ} {x}
       -> Shaped (f · x) -> Shaped x
unargˢ = inj₂ ∘ unargⁿᵉ ∘ unappˢ

unƛˢ : ∀ {Γ σ τ} {b : Γ ▻ σ ⊢ τ}
     -> Shaped (ƛ b) -> Shaped b
unƛˢ = smap (λ{(spⁿᵉ())}) unƛⁿᶠ

noβˢ : ∀ {Γ σ τ} {b : Γ ▻ σ ⊢ τ} {x}
     -> ¬ Shaped (ƛ b · x)
noβˢ = noβⁿᵉ ∘ unappˢ

decShaped : ∀ {Γ σ} -> (t : Γ ⊢ σ) -> Dec (Shaped t)
decShaped (var i) = yes (inj₁ (spⁿᵉ ø))
decShaped (ƛ b)   = map′ ƛˢ unƛˢ (decShaped b)
decShaped (f · x) with decShaped f | λ f′ -> map′ (appˢ f′) unargˢ (decShaped x)
... | yes (inj₁  f′)       | rec = rec f′
... | yes (inj₂ (neⁿᶠ f′)) | rec = rec f′
... | yes (inj₂ (ƛⁿᶠ  b′)) | rec = no  noβˢ
... | no   c               | rec = no (c ∘ unfunˢ)
decShaped  unit   = yes (inj₂ unitⁿᶠ)

decNf : ∀ {Γ σ} -> (t : Γ ⊢ σ) -> Dec (Nf t)
decNf = map′ nfˢ inj₂ ∘ decShaped
