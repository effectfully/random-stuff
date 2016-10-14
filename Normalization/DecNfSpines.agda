open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable

infixl 6 _▻_
infixr 6 _⇒_
infix  4 _⊢_ _∈_
infixl 7 _·_
infixl 5 _▷_

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
    appⁿᶠ  : ∀ {σ τ} {t : Γ ⊢ τ} -> (v : σ ∈ Γ) -> Spine v t -> Nf t
    ƛⁿᶠ    : ∀ {σ τ} {b : Γ ▻ σ ⊢ τ} -> Nf b -> Nf (ƛ b)
    unitⁿᶠ : Nf unit

  data Spine {Γ σ} (v : σ ∈ Γ) : ∀ {τ} -> Γ ⊢ τ -> Set where
    ø   : Spine v (var v)
    _▷_ : ∀ {τ ν} {t : Γ ⊢ τ ⇒ ν} {s : Γ ⊢ τ} -> Spine v t -> Nf s -> Spine v (t · s)

pattern _·ˢᵖ_ f x = appⁿᶠ _ (f ▷ x)

unƛⁿᶠ : ∀ {Γ σ τ} {b : Γ ▻ σ ⊢ τ}
      -> Nf (ƛ b) -> Nf b
unƛⁿᶠ (appⁿᶠ v ())
unƛⁿᶠ (ƛⁿᶠ b) = b

unfunⁿᶠ : ∀ {Γ σ τ} {f : Γ ⊢ σ ⇒ τ} {x}
        -> Nf (f · x) -> Nf f
unfunⁿᶠ (f ·ˢᵖ x) = appⁿᶠ _ f

unargⁿᶠ : ∀ {Γ σ τ} {f : Γ ⊢ σ ⇒ τ} {x}
        -> Nf (f · x) -> Nf x
unargⁿᶠ (f ·ˢᵖ x) = x

noβⁿᶠ : ∀ {Γ σ τ} {b : Γ ▻ σ ⊢ τ} {x}
      -> ¬ Nf (ƛ b · x)
noβⁿᶠ (() ·ˢᵖ x)

decNf : ∀ {Γ σ} -> (t : Γ ⊢ σ) -> Dec (Nf t)
decNf (var v) = yes (appⁿᶠ v ø)
decNf (ƛ b)   = map′ ƛⁿᶠ unƛⁿᶠ (decNf b)
decNf (f · x) with decNf f
... | yes (appⁿᶠ v sp) = map′ (sp ·ˢᵖ_) unargⁿᶠ (decNf x)
... | yes (ƛⁿᶠ  b′)    = no  noβⁿᶠ
... | no   c           = no (c ∘ unfunⁿᶠ)
decNf  unit   = yes unitⁿᶠ

module Translation where
  infix 4 _⊢ⁿᶠ_ _⊢ⁿᵉ_ _⊢ˢᵖ_∶_
  infixl 5 _▷_

  mutual
    data _⊢ⁿᶠ_ (Γ : Con) : Type → Set where
      neⁿᶠ   : ∀ {P}   → Γ ⊢ⁿᵉ P → Γ ⊢ⁿᶠ P
      lamⁿᶠ  : ∀ {A B} → Γ ▻ A ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ⇒ B
      unitⁿᶠ : Γ ⊢ⁿᶠ ι

    data _⊢ⁿᵉ_ (Γ : Con) : Type → Set where
      spⁿᵉ : ∀ {A C} → A ∈ Γ → Γ ⊢ˢᵖ A ∶ C → Γ ⊢ⁿᵉ C

    data _⊢ˢᵖ_∶_ (Γ : Con) : Type → Type → Set where
      ø   : ∀ {C}     → Γ ⊢ˢᵖ C ∶ C
      _▷_ : ∀ {A B C} → Γ ⊢ˢᵖ B ∶ C → Γ ⊢ⁿᶠ A → Γ ⊢ˢᵖ A ⇒ B ∶ C

  mutual
    coeⁿᶠ : ∀ {Γ σ} {t : Γ ⊢ σ} -> Nf t -> Γ ⊢ⁿᶠ σ
    coeⁿᶠ (appⁿᶠ v sp) = neⁿᶠ (spⁿᵉ v (coeˢᵖ ø sp))
    coeⁿᶠ (ƛⁿᶠ b)      = lamⁿᶠ (coeⁿᶠ b)
    coeⁿᶠ  unitⁿᶠ      = unitⁿᶠ

    coeˢᵖ : ∀ {Γ σ τ ν} {v : σ ∈ Γ} {t : Γ ⊢ τ} -> Γ ⊢ˢᵖ τ ∶ ν -> Spine v t -> Γ ⊢ˢᵖ σ ∶ ν
    coeˢᵖ a  ø       = a
    coeˢᵖ a (sp ▷ t) = coeˢᵖ (a ▷ coeⁿᶠ t) sp

  mine : ∀ {Γ σ τ ν δ} {t : Γ ⊢ σ} {s : Γ ⊢ τ} {u : Γ ⊢ ν}
       -> (v : σ ⇒ τ ⇒ ν ⇒ δ ∈ Γ) -> Nf t -> Nf s -> Nf u -> Nf (var v · t · s · u)
  mine v t s u = appⁿᶠ v (ø ▷ t ▷ s ▷ u)

  yours : ∀ {Γ σ τ ν δ} 
        -> (v : σ ⇒ τ ⇒ ν ⇒ δ ∈ Γ) -> Γ ⊢ⁿᶠ σ -> Γ ⊢ⁿᶠ τ -> Γ ⊢ⁿᶠ ν -> Γ ⊢ⁿᶠ δ
  yours v t s u = neⁿᶠ (spⁿᵉ v (ø ▷ u ▷ s ▷ t))
