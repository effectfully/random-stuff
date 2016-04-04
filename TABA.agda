-- Related to

-- "There and Back Again", Olivier Danvy, Mayer
-- Goldberg http://www.brics.dk/RS/05/3/BRICS-RS-05-3.pdf

-- and

-- ""There and Back Again" and What Happened After", Kenneth Foner
-- https://github.com/kwf/TABA-AWHA

open import Function
open import Data.Nat.Base
open import Data.Product
open import Data.Vec

data Diff n : ℕ -> ℕ -> Set where
  base : Diff n 0 n
  step : ∀ {m p} -> Diff n m (suc p) -> Diff n (suc m) p

same-go : (k : ℕ -> ℕ)
        -> (∀ {n m p} -> Diff n m (k (suc p)) -> Diff n m (suc (k p)))
        -> (n : ℕ)
        -> Diff (k n) n (k 0)
same-go k coe  0      = base
same-go k coe (suc n) = step (coe (same-go (k ∘ suc) coe n))

same : ∀ {n} -> Diff n n 0
same = same-go id id _

convolve : ∀ {α β n} {A : Set α} {B : Set β} -> Vec A n -> Vec B n -> Vec (A × B) n
convolve {n = n} {A} {B} xs ys = proj₁ (walk same xs) where
  walk : ∀ {m p} -> Diff n m p -> Vec A m -> Vec (A × B) m × Vec B p
  walk  base     []      = [] , ys
  walk (step d) (x ∷ xs) with walk d xs
  ... | ps , y ∷ ys' = ((x , y) ∷ ps) , ys'
