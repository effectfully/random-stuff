open import Level as Le
open import Function
open import Data.Unit
open import Data.Product hiding (map)
open import Data.Nat as N hiding (_⊔_)
open import Data.Vec

-- Universe polymorphic Vecs

N-ary-level-Vec : ∀ {n} -> Vec Level n -> Level -> Level
N-ary-level-Vec = flip $ foldr _ Le._⊔_

UVec : ∀ {n} -> (αs : Vec Level n) -> (γ : Level) -> Set (N-ary-level-Vec (map Le.suc αs) (Le.suc γ))
UVec  []      γ = Set γ
UVec (α ∷ αs) γ = Σ (Set α) (λ X -> X -> UVec αs γ)

N-ary-UVec : ∀ {n} {αs : Vec Level n} {γ} -> UVec αs γ -> Set (N-ary-level-Vec αs γ)
N-ary-UVec {αs = []}      Z      = Z
N-ary-UVec {αs = α ∷ αs} (X , F) = (x : X) -> N-ary-UVec (F x)

-- Auxiliary definitions

N-ary-UVec-impl : ∀ {n} {αs : Vec Level n} {β γ}
                -> UVec αs β -> Set γ -> Set (N-ary-level-Vec αs (β Le.⊔ γ))
N-ary-UVec-impl {αs = []}      Y      Z = Y -> Z
N-ary-UVec-impl {αs = α ∷ αs} (X , F) Z = {x : X} -> N-ary-UVec-impl (F x) Z

N-ary-UVec-impl-dep : ∀ {n} {αs : Vec Level n} {β γ}
                    -> (Xs : UVec αs β) -> N-ary-UVec-impl Xs (Set γ) -> Set (N-ary-level-Vec αs (β Le.⊔ γ))
N-ary-UVec-impl-dep {αs = []}      Y      Z = (y : Y) -> Z y
N-ary-UVec-impl-dep {αs = α ∷ αs} (X , F) Z = {x : X} -> N-ary-UVec-impl-dep (F x) Z

-- N-ary composition function

compT : ∀ {n} {αs : Vec Level n} {β γ}
      -> (Xs : UVec αs β)
      -> N-ary-UVec-impl Xs (Set γ)
      -> N-ary-UVec Xs
      -> Set (N-ary-level-Vec αs γ)
compT {αs = []}      Y      Z y = Z y
compT {αs = α ∷ αs} (X , F) Z f = ∀ x -> compT (F x) Z (f x)

comp' : ∀ {β γ n}
      -> (αs : Vec Level n) {Xs : UVec αs β} {Z : N-ary-UVec-impl Xs (Set γ)}
      -> N-ary-UVec-impl-dep Xs Z
      -> (f : N-ary-UVec Xs)
      -> compT Xs Z f
comp'  []      g y = g y
comp' (α ∷ αs) g f = comp' αs g ∘ f

-- "Currying"

_^_ : ∀ {α} -> Set α -> ℕ -> Set α
A ^ 0     = Lift ⊤
A ^ suc n = A × A ^ n

from-^ : ∀ {n α} {A : Set α} -> A ^ n -> Vec A n
from-^ {0}      _       = []
from-^ {suc n} (x , xs) = x ∷ from-^ xs

∀⇒ : ∀ {α n} {A : Set α} {k : Vec A n -> Level}
    -> (xs' : A ^ n)
    -> ((xs : Vec A n) -> Set (k xs))
    -> Set (k (from-^ xs'))
∀⇒ xs' B = B (from-^ xs')

λ⇒ : ∀ {α n} {A : Set α} {k : Vec A n -> Level} {B : (xs : Vec A n) -> Set (k xs)}
   -> (xs' : A ^ n)
   -> ((xs : Vec A n) -> B xs)
   -> ∀⇒ xs' B
λ⇒ xs' f = f (from-^ xs')

-- The final function

comp : ∀ {β γ}
     -> (n : ℕ) -> ∀ {αs'}
     -> ∀⇒ αs' (λ (αs : Vec Level n) -> {Xs : UVec αs β} {Z : N-ary-UVec-impl Xs (Set γ)}
               -> N-ary-UVec-impl-dep Xs Z
               -> (f : N-ary-UVec Xs)
               -> compT Xs Z f)
comp _ {αs'} = λ⇒ αs' comp'

-- Testing

length : ∀ {n α} {A : Set α} -> Vec A n -> ℕ
length {n} _ = n

comp-test-g : ∀ {n} -> (xs : Vec ℕ n) -> Vec ℕ (sum xs)
comp-test-g _  = replicate 2

comp-test-f : ∀ {n} -> (A : Set) -> Set₁ -> (xs : Vec A n) -> Vec ℕ (length xs)
comp-test-f _ _ _ = replicate 1

test-comp : ∀ {n} -> (A : Set) -> Set₁ -> (xs : Vec A n) -> Vec ℕ (sum (replicate {n = length xs} 1))
test-comp = comp 3 comp-test-g comp-test-f

comp-test-g' : ℕ -> ℕ
comp-test-g' _ = 0

comp-test-f' : ((ℕ -> Set) -> ℕ) -> ℕ -> ℕ
comp-test-f' _ _ = 0

test-comp' : ((ℕ -> Set) -> ℕ) -> ℕ -> ℕ
test-comp' = comp 2 comp-test-g' comp-test-f'
