-- A categorical view of STLC.

open import Data.Unit.Base
open import Data.Product

infixr 6 _⇒_
infixr 7 _&_
infix  4 _⊢_

data Type : Set where
  ⋆   : Type
  _⇒_ : Type -> Type -> Type
  _&_ : Type -> Type -> Type

data _⊢_ : Type -> Type -> Set where
  ƛ_   : ∀ {Γ σ τ} -> Γ & σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _·_  : ∀ {Γ σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ
  unit : ∀ {Γ}     -> Γ ⊢ ⋆
  pair : ∀ {Γ σ τ} -> Γ ⊢ σ     -> Γ ⊢ τ     -> Γ ⊢ σ & τ
  fst  : ∀ {Γ σ τ} -> Γ ⊢ σ & τ -> Γ ⊢ σ
  snd  : ∀ {Γ σ τ} -> Γ ⊢ σ & τ -> Γ ⊢ τ
  vz   : ∀ {Γ σ}   -> Γ & σ ⊢ σ
  ↑    : ∀ {Γ σ}   -> Γ & σ ⊢ Γ
  _[_] : ∀ {Δ Γ σ} -> Γ ⊢ σ     -> Δ ⊢ Γ     -> Δ ⊢ σ

⟦_⟧ : Type -> Set
⟦ ⋆     ⟧ = ⊤
⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ -> ⟦ τ ⟧
⟦ Γ & σ ⟧ = ⟦ Γ ⟧ × ⟦ σ ⟧

⟦_/_⟧ : ∀ {Γ σ} -> ⟦ Γ ⟧ -> Γ ⊢ σ -> ⟦ σ ⟧
⟦ ρ     / ƛ b      ⟧ = λ x -> ⟦ ρ , x / b ⟧
⟦ ρ     / f · x    ⟧ = ⟦ ρ / f ⟧ ⟦ ρ / x ⟧
⟦ ρ     / unit     ⟧ = tt
⟦ ρ     / pair t s ⟧ = ⟦ ρ / t ⟧ , ⟦ ρ / s ⟧
⟦ ρ     / fst p    ⟧ = proj₁ ⟦ ρ / p ⟧
⟦ ρ     / snd p    ⟧ = proj₂ ⟦ ρ / p ⟧
⟦ ρ , x / vz       ⟧ = x
⟦ ρ , x / ↑        ⟧ = ρ
⟦ ρ     / t [ ψ ]  ⟧ = ⟦ ⟦ ρ / ψ ⟧ / t ⟧

eval : ∀ {σ} -> ⋆ ⊢ σ -> ⟦ σ ⟧
eval t = ⟦ tt / t ⟧
