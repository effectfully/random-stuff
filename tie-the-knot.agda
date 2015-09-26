open import Function
open import Data.Nat
open import Data.Product
open import Data.Vec

{-# NON_TERMINATING #-}
fix : ∀ {α} {A : Set α} -> (A -> A) -> A
fix f = f (fix f)

3∷3∷3∷[] : Vec ℕ _
3∷3∷3∷[] = proj₂ (fix (uncurry (const ∘ f))) where
  f : ℕ -> ∃ (Vec ℕ)
  f m = 3 , replicate m
