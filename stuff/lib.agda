open import Level
open import Function hiding (const)
open import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.HeterogeneousEquality as H hiding (subst₂)
open import Data.Product

const : ∀ {α β} {A : Set α} {B : A -> Set β} -> (x : A) -> B x -> A
const x = λ _ -> x

-- Is it in the standard library? I cannot find.
_<->_ : ∀ {α β} -> Set α -> Set β -> Set (α ⊔ β)
A <-> B = (A -> B) × (B -> A)

subst-removable-cool : ∀ {α β γ} {I : Set α} {i j : I}
                     -> (A : I -> Set β) {B : {k : I} -> A k -> Set γ} {x : A i}
                     -> (f : {k : I} -> (x : A k) -> B x)
                     -> (i≅j : i ≅ j) {y : B (H.subst A i≅j x)}
                     -> f (H.subst A i≅j x) ≅ y
                     -> f x ≅ y
subst-removable-cool A f refl r = r

unsubst : ∀ {ι α} {I : Set ι} {A : I -> Set α} {i j : I} (i≡j : i ≡ j) {x : A i} {y : A j}
        -> P.subst A i≡j x ≡ y -> x ≅ y
unsubst refl refl = refl

subst-removable-cong : ∀ {ι α β} {I : Set ι} {B : Set β} {i j : I}
                     -> (A : I -> Set α)
                     -> (i≡j : i ≡ j)
                     -> (x : A i)
                     -> (f : ∀ {k} -> A k -> B)
                     -> f (P.subst A i≡j x) ≡ f x
subst-removable-cong A refl x f = refl

subst-removable-id : ∀ {ι α} {I : Set ι} {b : I -> Level} {i j : I}
                   -> (A : I -> Set α)
                   -> (i≡j : i ≡ j)
                   -> (x : A i)
                   -> (F : ∀ {k} -> A k -> Set (b k))
                   -> F (P.subst A i≡j x) <-> F x
subst-removable-id A refl x F = id , id

subst₂ : ∀ {α β γ} {A : Set α} {B : A -> Set β} {x y} {v w}
       -> (C : ∀ x -> B x -> Set γ) -> x ≅ y -> v ≅ w -> C x v -> C y w
subst₂ C refl refl = id

isubst : ∀ {ι α β} {I : Set ι} {i j : I}
         (A : I -> Set α) {x : A i} {y : A j}
       -> (B : ∀ {k} -> A k -> Set β) -> i ≅ j -> x ≅ y -> B x -> B y
isubst A C refl refl = id

icong : ∀ {ι α β} {I : Set ι} {i j : I}
        (A : I -> Set α) {B : ∀ {k} -> A k -> Set β} {x : A i} {y : A j}
      -> (f : ∀ {k} -> (x : A k) -> B x) -> i ≅ j -> x ≅ y -> f x ≅ f y
icong A f refl refl = refl

icong² : ∀ {ι₁ ι₂ α β} {I₁ : Set ι₁} {I₂ : I₁ -> Set ι₂}
         (A : ∀ i₁ -> I₂ i₁ -> Set α) {B : ∀ {i₁ i₂} -> A i₁ i₂ -> Set β}
         {i₁ i₂ j₁ j₂} {x : A i₁ i₂} {y : A j₁ j₂}
       -> (f : ∀ {i₁ i₂} -> (x : A i₁ i₂) -> B x)
       -> i₁ ≅ j₁ -> i₂ ≅ j₂ -> x ≅ y -> f x ≅ f y
icong² A f refl refl refl = refl

icong³ : ∀ {ι₁ ι₂ ι₃ α β} {I₁ : Set ι₁} {I₂ : I₁ -> Set ι₂}
         {I₃ : ∀ {i₁} -> I₂ i₁ -> Set ι₃}
         (A : ∀ i₁ -> (i₂ : I₂ i₁) -> I₃ i₂ -> Set α)
         {B : ∀ {i₁ i₂ i₃} -> A i₁ i₂ i₃ -> Set β}
         {i₁ i₂ i₃ j₁ j₂ j₃} {x : A i₁ i₂ i₃} {y : A j₁ j₂ j₃}
       -> (f : ∀ {i₁ i₂ i₃} -> (x : A i₁ i₂ i₃) -> B x)
       -> i₁ ≅ j₁ -> i₂ ≅ j₂ -> i₃ ≅ j₃ -> x ≅ y -> f x ≅ f y
icong³ A f refl refl refl refl = refl

icong₂ : ∀ {ι α β γ} {I : Set ι}
         (A : I -> Set α) {B : ∀ {k} -> A k -> Set β}
         {C : ∀ {k} -> (x : A k) -> B x -> Set γ}
         {i j} {x : A i} {y : A j} {v w}
       -> (f : ∀ {k} -> (x : A k) -> (y : B x) -> C x y)
       -> i ≅ j -> x ≅ y -> v ≅ w -> f x v ≅ f y w
icong₂ A f refl refl refl = refl

icong²₂ : ∀ {ι₁ ι₂ α β γ} {I₁ : Set ι₁} {I₂ : I₁ -> Set ι₂}
          (A : ∀ i₁ -> I₂ i₁ -> Set α) {B : ∀ {i₁ i₂} -> A i₁ i₂ -> Set β}
          {C : ∀ {i₁ i₂} {x : A i₁ i₂} -> B x -> Set γ}
          {i₁ i₂ j₁ j₂} {x : A i₁ i₂} {y : A j₁ j₂} {v w}
        -> (f : ∀ {i₁ i₂} -> (x : A i₁ i₂) -> (y : B x) -> C y)
        -> i₁ ≅ j₁ -> i₂ ≅ j₂ -> x ≅ y -> v ≅ w -> f x v ≅ f y w
icong²₂ A f refl refl refl refl = refl
