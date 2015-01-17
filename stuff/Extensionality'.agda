open import Level as Le
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Product hiding (map)
open import Data.Nat as N hiding (_⊔_)
open import Data.Vec

N-ary-level-Vec' : ∀ {n} -> Vec Level n -> Level -> Level
N-ary-level-Vec' = flip $ foldr _ Le._⊔_

UVec' : ∀ {n} (αs : Vec Level n) γ -> Set (N-ary-level-Vec' (map Le.suc αs) (Le.suc γ))
UVec'  []      γ = Set γ
UVec' (α ∷ αs) γ = Σ (Set α) (λ X -> X -> UVec' αs γ)

N-ary-UVec : ∀ {n} {αs : Vec Level n} {γ} -> UVec' αs γ -> Set (N-ary-level-Vec' αs γ)
N-ary-UVec {αs = []}      Z      = Z
N-ary-UVec {αs = α ∷ αs} (X , F) = (x : X) -> N-ary-UVec (F x)

_^_ : ∀ {α} -> Set α -> ℕ -> Set α
A ^ 0     = Lift ⊤
A ^ suc n = A × A ^ n

from-^ : ∀ {n α} {A : Set α} -> A ^ n -> Vec A n
from-^ {0}      _       = []
from-^ {suc n} (x , xs) = x ∷ from-^ xs

UVec : ∀ {n}
     -> (αs : Level ^ n)
     -> (γ : Level)
     -> Set (N-ary-level-Vec' (map Le.suc (from-^ αs)) (Le.suc γ))
UVec αs = UVec' (from-^ αs)

N-ary-level-Vec : ∀ {n} -> Level ^ n -> Level -> Level
N-ary-level-Vec αs = N-ary-level-Vec' (from-^ αs)


_[]⇒_≡ₑ_ : ∀ {n γ} (αs : Vec Level n) {Xs : UVec' αs γ}
         -> N-ary-UVec Xs -> N-ary-UVec Xs -> Set (N-ary-level-Vec' αs γ)
[]       []⇒ x ≡ₑ y = x ≡ y
(α ∷ αs) []⇒ f ≡ₑ g = ∀ x -> αs []⇒ f x ≡ₑ g x

data _⇒_≡ₑ_ n {γ} {αs : Level ^ n} {Xs : UVec αs γ} (f : N-ary-UVec Xs) :
  N-ary-UVec Xs -> Set (N-ary-level-Vec αs γ) where
    reflₑ : ∀ {g} -> from-^ αs []⇒ f ≡ₑ g -> n ⇒ f ≡ₑ g



_[]~ₑ_ : ∀ {n γ} {αs : Vec Level n} {Xs : UVec' αs γ} {f g h : N-ary-UVec Xs}
       -> αs []⇒ f ≡ₑ g -> αs []⇒ g ≡ₑ h -> αs []⇒ f ≡ₑ h
_[]~ₑ_ {αs = []}     refl refl = refl
_[]~ₑ_ {αs = α ∷ αs} p    q    = λ x -> p x []~ₑ q x

_~ₑ_ : ∀ {n γ} {αs : Level ^ n} {Xs : UVec αs γ} {f g h : N-ary-UVec Xs}
     -> n ⇒ f ≡ₑ g -> n ⇒ g ≡ₑ h -> n ⇒ f ≡ₑ h
reflₑ p ~ₑ reflₑ q = reflₑ (p []~ₑ q)

module _ where
  private
    postulate
      Extensionality' : ∀ {n γ} {αs : Level ^ n} {Xs : UVec αs γ} {f g : N-ary-UVec Xs}
                      -> n ⇒ f ≡ₑ g -> f ≡ g

[]E->E' : ∀ {n γ} {αs : Vec Level n} {Xs : UVec' αs γ} {f g : N-ary-UVec Xs}
        -> (∀ {α β} {A : Set α} {B : A -> Set β} {f g : (x : A) -> B x}
            -> (∀ x -> f x ≡ g x) -> f ≡ g)
        -> αs []⇒ f ≡ₑ g -> f ≡ g
[]E->E' {αs = []}     E refl = refl
[]E->E' {αs = α ∷ αs} E p    = E λ x -> []E->E' E (p x)

E->E' :  (∀ {α β} {A : Set α} {B : A -> Set β} {f g : (x : A) -> B x}
          -> (∀ x -> f x ≡ g x) -> f ≡ g)
      -> (∀ {n γ} {αs : Level ^ n} {Xs : UVec αs γ} {f g : N-ary-UVec Xs}
          -> n ⇒ f ≡ₑ g -> f ≡ g)
E->E' E (reflₑ p) = []E->E' E p

E'->E :  (∀ {n γ} {αs : Level ^ n} {Xs : UVec αs γ} {f g : N-ary-UVec Xs}
          -> n ⇒ f ≡ₑ g -> f ≡ g)
      -> (∀ {α β} {A : Set α} {B : A -> Set β} {f g : (x : A) -> B x}
          -> (∀ x -> f x ≡ g x) -> f ≡ g)
E'->E E' p = E' (reflₑ p)



+0 : (n : ℕ) -> n ≡ n + 0
+0  0      = refl
+0 (suc n) = cong N.suc (+0 n)  

example : 1 ⇒ (λ n -> 0 + n) ≡ₑ (λ n -> n + 0)
example = reflₑ +0
