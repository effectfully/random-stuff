open import Function
open import Relation.Nullary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Sum
open import Data.Product

delim : ∀ {α β} {A : Set α} {B : Dec A -> Set β}
      -> (d : Dec A) -> (∀ x -> B (yes x)) -> (∀ c -> B (no c)) -> B d
delim (yes x) f g = f x
delim (no  c) f g = g c

drec = λ {α β} {A : Set α} {B : Set β} -> delim {A = A} {B = λ _ -> B}

dcong₂ : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ} {x y v w}
       -> (f : A -> B -> C)
       -> (∀ {x y} -> f x v ≡ f y w -> x ≡ y × v ≡ w)
       -> Dec (x ≡ y)
       -> Dec (v ≡ w)
       -> Dec (f x v ≡ f y w)
dcong₂ f inj d₁ d₂ = drec d₁
    (λ p₁ -> drec d₂
      (λ p₂ -> yes (cong₂ f p₁ p₂))
      (λ c  -> no (c ∘ proj₂ ∘ inj)))
    (λ c  -> no (c ∘ proj₁ ∘ inj))

infixl 5 _▻_
infixr 5 _⇒_
infix  4 _≟ᵗ_ _≟ᶜ_ _∈_ _⊢_ _⊂[_]_ _⊂?_

data Type : Set where
  ⋆   : Type
  _⇒_ : Type -> Type -> Type

data Con : Set where
  ε   : Con
  _▻_ : Con -> Type -> Con

data _∈_ σ : Con -> Set where
  vz : ∀ {Γ}   -> σ ∈ Γ ▻ σ
  vs : ∀ {Γ τ} -> σ ∈ Γ     -> σ ∈ Γ ▻ τ 

data _⊢_ Γ : Type -> Set where
  var : ∀ {σ}   -> σ ∈ Γ     -> Γ ⊢ σ
  ƛ   : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _·_ : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ

⇒-inj : ∀ {σ₁ σ₂ τ₁ τ₂} -> σ₁ ⇒ τ₁ ≡ σ₂ ⇒ τ₂ -> σ₁ ≡ σ₂ × τ₁ ≡ τ₂
⇒-inj refl = refl , refl

▻-inj : ∀ {Γ₁ Γ₂ σ₁ σ₂} -> Γ₁ ▻ σ₁ ≡ Γ₂ ▻ σ₂ -> Γ₁ ≡ Γ₂ × σ₁ ≡ σ₂
▻-inj refl = refl , refl

_≟ᵗ_ : Decidable (_≡_ {A = Type})
⋆         ≟ᵗ ⋆         = yes refl
(σ₁ ⇒ τ₁) ≟ᵗ (σ₂ ⇒ τ₂) = dcong₂ _⇒_ ⇒-inj (σ₁ ≟ᵗ σ₂) (τ₁ ≟ᵗ τ₂)
⋆         ≟ᵗ (σ₂ ⇒ τ₂) = no λ()
(σ₁ ⇒ τ₁) ≟ᵗ ⋆         = no λ()

_≟ᶜ_ : Decidable (_≡_ {A = Con})
ε     ≟ᶜ ε     = yes refl
Γ ▻ σ ≟ᶜ Δ ▻ τ = dcong₂ _▻_ ▻-inj (Γ ≟ᶜ Δ) (σ ≟ᵗ τ)
ε     ≟ᶜ Δ ▻ τ = no λ()
Γ ▻ σ ≟ᶜ ε     = no λ()

data _⊂[_]_ : Con -> Type -> Con -> Set where
  stop : ∀ {Γ σ}     -> Γ ⊂[ σ ] Γ ▻ σ
  skip : ∀ {Γ Δ σ τ} -> Γ ⊂[ σ ] Δ     -> Γ ⊂[ σ ] Δ ▻ τ

sub : ∀ {Γ Δ σ} -> Γ ⊂[ σ ] Δ -> σ ∈ Δ
sub  stop    = vz
sub (skip p) = vs (sub p)

⊂-inj : ∀ {Γ Δ σ τ} -> Γ ⊂[ σ ] Δ ▻ τ -> Γ ⊂[ σ ] Δ ⊎ Γ ≡ Δ × σ ≡ τ
⊂-inj  stop    = inj₂ (refl , refl)
⊂-inj (skip p) = inj₁ p

_⊂?_ : ∀ {σ} -> Decidable _⊂[ σ ]_
_⊂?_     Γ  ε      = no λ()
_⊂?_ {σ} Γ (Δ ▻ τ) with λ c₁ -> drec (Γ ⊂? Δ) (yes ∘ skip) (λ c₂ -> no ([ c₂ , c₁ ] ∘ ⊂-inj))
... | r with σ ≟ᵗ τ
... | no  c₁ = r (c₁ ∘ proj₂)
... | yes p₁ rewrite p₁ with Γ ≟ᶜ Δ
... | no  c₁ = r (c₁ ∘ proj₁)
... | yes p₂ rewrite p₂ = yes stop

Term : Type -> Set
Term σ = ε ⊢ σ

⊢_ : Type -> Set
⊢ σ = ∀ {Γ} -> Γ ⊢ σ

⟦_⟧ : Type -> Set
⟦ ⋆     ⟧ = ⊢ ⋆
⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ -> ⟦ τ ⟧

mutual
  ↑ : ∀ {σ} -> ⊢ σ -> ⟦ σ ⟧
  ↑ {⋆}     t = t
  ↑ {σ ⇒ τ} f = λ x -> ↑ (f · ↓ x)

  ↓ : ∀ {σ} -> ⟦ σ ⟧ -> ⊢ σ
  ↓ {⋆}     t = t
  ↓ {σ ⇒ τ} f = λ {Γ} -> ƛ (↓ (f (↑ (λ {Δ} -> var (diff Δ Γ σ))))) where

    diff : ∀ Δ Γ σ -> σ ∈ Δ
    diff Δ Γ σ = drec (Γ ⊂? Δ) sub impossible where
      postulate impossible : _



I : Term (⋆ ⇒ ⋆)
I = ↓ id

K : Term (⋆ ⇒ ⋆ ⇒ ⋆)
K = ↓ const

S : Term ((⋆ ⇒ ⋆ ⇒ ⋆) ⇒ (⋆ ⇒ ⋆) ⇒ ⋆ ⇒ ⋆)
S = ↓ _ˢ_

B : Term ((⋆ ⇒ ⋆) ⇒ (⋆ ⇒ ⋆) ⇒ ⋆ ⇒ ⋆)
B = ↓ _∘′_

C : Term ((⋆ ⇒ ⋆ ⇒ ⋆) ⇒ ⋆ ⇒ ⋆ ⇒ ⋆)
C = ↓ flip

W : Term ((⋆ ⇒ ⋆ ⇒ ⋆) ⇒ ⋆ ⇒ ⋆)
W = ↓ λ f x -> f x x

P : Term ((⋆ ⇒ ⋆ ⇒ ⋆) ⇒ (⋆ ⇒ ⋆) ⇒ ⋆ ⇒ ⋆ ⇒ ⋆)
P = ↓ _on_

O : Term (((⋆ ⇒ ⋆) ⇒ ⋆) ⇒ (⋆ ⇒ ⋆) ⇒ ⋆)
O = ↓ λ g f -> f (g f)
