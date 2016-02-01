module Effect.HState where

open import Prelude

open import Data.Maybe.Base

Effect : ∀ {ρ ψ φ}
       -> (F : Set ρ -> Set ψ)
       -> (∀ {R} -> F R -> Set φ)
       -> ∀ ε
       -> Set (ψ ⊔ φ ⊔ lsuc (ρ ⊔ ε))
Effect {ρ} F G ε = (R : Set ρ) -> (A : F R) -> (G A -> Set ρ) -> Set ε

Constr : ∀ {ρ} -> Set ρ -> Set (lsuc ρ)
Constr R = Maybe (R ≡ ⊤)

State : ∀ {ρ} -> Effect Constr (λ {R} _ -> R) ρ
State R  nothing    R′ = ⊤
State _ (just refl) R′ = R′ _
