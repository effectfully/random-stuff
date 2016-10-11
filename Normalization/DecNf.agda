open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Product
open import Data.Nat.Base
open import Data.Fin
open import Data.Sum renaming (map to smap)
open import Data.Product

fromInj₁ : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> A ⊎ B -> B
fromInj₁ f = [ f , id ]′

fromInj₂ : ∀ {α β} {A : Set α} {B : Set β} -> (B -> A) -> A ⊎ B -> A
fromInj₂ g = [ id , g ]′

infixl 6 _▻_
infixr 6 _⇒_
infix  4 _⊢_
infixl 7 _·_

data Type : Set where
  ι   : Type
  _⇒_ : Type -> Type -> Type

Con : ℕ -> Set
Con n = Fin n -> Type

_▻_ : ∀ {n} -> Con n -> Type -> Con (suc n)
(Γ ▻ σ)  zero   = σ
(Γ ▻ σ) (suc i) = Γ i

data _⊢_ {n} (Γ : Con n) : Type -> Set where
  var  : ∀ i -> Γ ⊢ Γ i
  ƛ    : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _·_  : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ -> Γ ⊢ τ
  unit : Γ ⊢ ι

mutual
  data Ne {n} {Γ : Con n} : ∀ {σ} -> Γ ⊢ σ -> Set where
    varⁿᵉ  : ∀ {i} -> Ne {Γ = Γ} (var i)
    _·ⁿᵉ_  : ∀ {σ τ} {f : Γ ⊢ σ ⇒ τ} {x} -> Ne f -> Nf x -> Ne (f · x)

  data Nf {n} {Γ : Con n} : ∀ {σ} -> Γ ⊢ σ -> Set where
    neⁿᶠ   : ∀ {σ} {t : Γ ⊢ σ} -> Ne t -> Nf t
    ƛⁿᶠ    : ∀ {σ τ} {b : Γ ▻ σ ⊢ τ} -> Nf b -> Nf (ƛ b)
    unitⁿᶠ : Nf {Γ = Γ} unit

Shaped : ∀ {n σ} {Γ : Con n} -> Γ ⊢ σ -> Set
Shaped t = Ne t ⊎ Nf t

nfˢ : ∀ {n σ} {Γ : Con n} {t : Γ ⊢ σ}
    -> Shaped t -> Nf t
nfˢ = fromInj₁ neⁿᶠ

appˢ : ∀ {n σ τ} {Γ : Con n} {f : Γ ⊢ σ ⇒ τ} {x}
     -> Ne f -> Shaped x -> Shaped (f · x)
appˢ f = inj₁ ∘ _·ⁿᵉ_ f ∘ nfˢ

ƛˢ : ∀ {n σ τ} {Γ : Con n} {b : Γ ▻ σ ⊢ τ}
   -> Shaped b -> Shaped (ƛ b)
ƛˢ = inj₂ ∘ ƛⁿᶠ ∘ nfˢ

unappⁿᶠ : ∀ {n σ τ} {Γ : Con n} {f : Γ ⊢ σ ⇒ τ} {x}
        -> Nf (f · x) -> Ne (f · x)
unappⁿᶠ (neⁿᶠ t) = t

unfunⁿᵉ : ∀ {n σ τ} {Γ : Con n} {f : Γ ⊢ σ ⇒ τ} {x}
        -> Ne (f · x) -> Ne f
unfunⁿᵉ (f ·ⁿᵉ x) = f

unargⁿᵉ : ∀ {n σ τ} {Γ : Con n} {f : Γ ⊢ σ ⇒ τ} {x}
        -> Ne (f · x) -> Nf x
unargⁿᵉ (f ·ⁿᵉ x) = x

unƛⁿᶠ : ∀ {n σ τ} {Γ : Con n} {b : Γ ▻ σ ⊢ τ}
      -> Nf (ƛ b) -> Nf b
unƛⁿᶠ (neⁿᶠ ())
unƛⁿᶠ (ƛⁿᶠ b) = b

noβⁿᵉ : ∀ {n σ τ} {Γ : Con n} {b : Γ ▻ σ ⊢ τ} {x}
      -> ¬ Ne (ƛ b · x)
noβⁿᵉ (() ·ⁿᵉ _)

unappˢ : ∀ {n σ τ} {Γ : Con n} {f : Γ ⊢ σ ⇒ τ} {x}
       -> Shaped (f · x) -> Ne (f · x)
unappˢ = fromInj₂ unappⁿᶠ

unfunˢ : ∀ {n σ τ} {Γ : Con n} {f : Γ ⊢ σ ⇒ τ} {x}
       -> Shaped (f · x) -> Shaped f
unfunˢ = inj₁ ∘ unfunⁿᵉ ∘ unappˢ

unargˢ : ∀ {n σ τ} {Γ : Con n} {f : Γ ⊢ σ ⇒ τ} {x}
       -> Shaped (f · x) -> Shaped x
unargˢ = inj₂ ∘ unargⁿᵉ ∘ unappˢ

unƛˢ : ∀ {n σ τ} {Γ : Con n} {b : Γ ▻ σ ⊢ τ}
     -> Shaped (ƛ b) -> Shaped b
unƛˢ = smap (λ()) unƛⁿᶠ

noβˢ : ∀ {n σ τ} {Γ : Con n} {b : Γ ▻ σ ⊢ τ} {x}
     -> ¬ Shaped (ƛ b · x)
noβˢ = noβⁿᵉ ∘ unappˢ

decShaped : ∀ {n σ} {Γ : Con n} -> (t : Γ ⊢ σ) -> Dec (Shaped t)
decShaped (var i) = yes (inj₁ varⁿᵉ)
decShaped (ƛ b)   = map′ ƛˢ unƛˢ (decShaped b)
decShaped (f · x) with decShaped f | λ f′ -> map′ (appˢ f′) unargˢ (decShaped x)
... | yes (inj₁  f′)       | rec = rec f′
... | yes (inj₂ (neⁿᶠ f′)) | rec = rec f′
... | yes (inj₂ (ƛⁿᶠ  b′)) | rec = no  noβˢ
... | no   c               | rec = no (c ∘ unfunˢ)
decShaped  unit   = yes (inj₂ unitⁿᶠ)

decNf : ∀ {n σ} {Γ : Con n} -> (t : Γ ⊢ σ) -> Dec (Nf t)
decNf = map′ nfˢ inj₂ ∘ decShaped
