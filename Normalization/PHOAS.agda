open import Function

record Tag {α β} {A : Set α} (B : (x : A) -> Set β) (x : A) : Set β where
  constructor tag
  field detag : B x
open Tag

tagWith : ∀ {α β} {A : Set α} {B : (x : A) -> Set β} -> (x : A) -> B x -> Tag B x
tagWith _ = tag

infixr 5 _⇒_

data Type : Set where
  ⋆   : Type
  _⇒_ : Type -> Type -> Type

data PTerm (V : Type -> Set) : Type -> Set where
  val : ∀ {σ} -> Tag V σ -> PTerm V σ
  lam : ∀ {σ τ} -> (Tag V σ -> PTerm V τ) -> PTerm V (σ ⇒ τ)
  app : ∀ {σ τ} -> PTerm V (σ ⇒ τ) -> PTerm V σ -> PTerm V τ

⟦_/_⟧ : (Type -> Set) -> Type -> Set
⟦ V / ⋆     ⟧ = V ⋆
⟦ V / σ ⇒ τ ⟧ = ⟦ V / σ ⟧ -> ⟦ V / τ ⟧

mutual
  ↑ : ∀ {σ V} -> PTerm V σ -> ⟦ PTerm V / σ ⟧
  ↑ {⋆}     t = t
  ↑ {σ ⇒ τ} f = ↑ ∘ app f ∘ ↓

  ↓ : ∀ {σ V} -> ⟦ PTerm V / σ ⟧ -> PTerm V σ
  ↓ {⋆}     t = t
  ↓ {σ ⇒ τ} f = lam (↓ ∘ f ∘ ↑ ∘ val)

Term : Type -> Set₁
Term σ = ∀ {V} -> PTerm V σ



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
