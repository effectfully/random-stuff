module System-F.TypeEval where

open import System-F.Prelude
open import System-F.Sets
open import System-F.Kits
open import System-F.Core

Levels : ∀ {Θ σ} -> Θ ⊢ᵗ σ -> Set
Levels (Var v)  = ⊤
Levels (f ·ᵗ α) = ⊥
Levels (α ⇒ β)  = Levels α × Levels β
Levels (π σ β)  = Level × Levels β
Levels  list    = ⊥

⟦_⟧ᵗˡ : ∀ {Θ} -> (α : Type Θ) -> Levels α -> Level ^ lengthᶜ Θ -> Level
⟦ Var v  ⟧ᵗˡ  _          bs = on-^ (lookup (∈-to-Fin v)) bs
⟦ f ·ᵗ α ⟧ᵗˡ ()
⟦ α ⇒ β  ⟧ᵗˡ (fs₁ , fs₂) bs = ⟦ α ⟧ᵗˡ fs₁ bs ⊔ ⟦ β ⟧ᵗˡ fs₂ bs
⟦ π σ β  ⟧ᵗˡ (f , fs)    bs = sucₗ f ⊔ ⟦ β ⟧ᵗˡ fs (f , bs)

⟦_⟧ᵗ : ∀ {Θ} {bs : Level ^ lengthᶜ Θ}
     -> (α : Type Θ) -> (fs : Levels α) -> Sets bs -> Set (⟦ α ⟧ᵗˡ fs bs)
⟦ Var v  ⟧ᵗ  _          As = Lookup (∈-to-Fin v) As
⟦ f ·ᵗ α ⟧ᵗ ()
⟦ α ⇒ β  ⟧ᵗ (fs₁ , fs₂) As = ⟦ α ⟧ᵗ fs₁ As -> ⟦ β ⟧ᵗ fs₂ As 
⟦ π σ β  ⟧ᵗ (f , fs)    As = {A : Set f} -> ⟦ β ⟧ᵗ fs (A , As)

evalᵗ : (α : Type ε) {fs : Levels α} -> Set (⟦ α ⟧ᵗˡ fs _)
evalᵗ α {fs} = ⟦ α ⟧ᵗ fs _



ex : Type⁺
ex = π ⋆ $ π ⋆ $ Var (vs vz) ⇒ π ⋆ (Var (vs vs vz) ⇒ Var vz) ⇒ Var vz

test : ∀ {α β γ} -> evalᵗ ex ≡ ({A : Set α} {B : Set β} -> A -> ({C : Set γ} -> A -> C) -> B)
test = refl
