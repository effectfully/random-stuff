open import Function
open import Data.Nat.Base
open import Data.Fin hiding (_+_; #_)

data Syntax n : Set where
  var : Fin n -> Syntax n
  ƛ_  : Syntax (suc n) -> Syntax n
  _·_ : Syntax n -> Syntax n -> Syntax n

shift : ∀ {m} n -> Fin (suc (n + m))
shift  0      = fromℕ _
shift (suc n) = inject₁ (shift n)

Bound : ℕ -> Set
Bound n = ∀ {m} -> Syntax (suc (n + m))

Bindᶜ : (ℕ -> ℕ) -> ℕ -> Set
Bindᶜ k  0      = Syntax (k 0)
Bindᶜ k (suc n) = Bound (k 0) -> Bindᶜ (k ∘ suc) n

bindᶜ : ∀ k n -> Bindᶜ k n -> Syntax (k n)
bindᶜ k  0      b = b
bindᶜ k (suc n) b = bindᶜ (k ∘ suc) n (b (var (shift (k 0))))

ƛⁿ : ∀ {m} n -> Syntax (n + m) -> Syntax m
ƛⁿ  0      e = e
ƛⁿ (suc n) e = ƛⁿ n (ƛ e)

_#_ : ∀ {n} m -> Bindᶜ (flip _+_ n) m -> Syntax n
_#_ {n} m b = ƛⁿ m (bindᶜ (flip _+_ n) m b)

example : Syntax 0
example = 3 # λ h f x → (1 # λ t → t · h) · (f · x)
