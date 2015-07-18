module Categories.Examples where

import Function as F
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Data.List.Base
open import Data.List.Properties

open import Categories.Setoid
open import Categories.Category
open import Categories.Functor

open Setoid-Instances _

∘′-resp-≡ : ∀ {α} {A B C : Set α} {g₁ g₂ : B -> C} {f₁ f₂ : A -> B}
          -> (∀ y -> g₁ y ≡ g₂ y) -> (∀ x -> f₁ x ≡ f₂ x) -> ∀ x -> g₁ (f₁ x) ≡ g₂ (f₂ x)
∘′-resp-≡ q p x rewrite p x = q _

instance
  Agda : ∀ {α} -> IsCategory (λ (A B : Set α) -> A -> B)
  Agda = record
    { id       = F.id
    ; _∘_      = F._∘′_
    ; idˡ      = λ x -> P.refl
    ; idʳ      = λ x -> P.refl
    ; assoc    = λ f x -> P.refl
    ; ∘-resp-≈ = ∘′-resp-≡
    }

  →-IsEndofunctor : ∀ {α} {R : Set α} -> IsEndofunctor (λ (A B : Set α) -> A -> B) (λ Q -> R -> Q)
  →-IsEndofunctor {α} {C} = record
    { F₁       = F._∘′_
    ; F-id     = λ x -> P.refl
    ; F-∘      = λ x -> P.refl
    ; F-resp-≈ = λ p f -> ext (λ x -> p (f x))
    } where postulate ext : P.Extensionality _ _

  List-IsEndofunctor : ∀ {α} -> IsEndofunctor (λ (A B : Set α) -> A -> B) List
  List-IsEndofunctor = record
    { F₁       = map
    ; F-id     = map-id
    ; F-∘      = map-compose
    ; F-resp-≈ = map-cong
    }

module Test where
  open IsFunctor {{...}}

  -- open IsFunctor {{...}} renaming (F₁ to _<$>_)

  _<$>_ : ∀ {α β} {Obj : Set α} {_⇒_ : Obj -> Obj -> Set β} {A B : Obj} {F₀ : Obj -> Obj}
            {{setoid : ∀ {A B} -> Setoid (A ⇒ B)}} {{C : IsCategory _⇒_ {{setoid}}}}
            {{isEndofunctor : IsEndofunctor _⇒_ F₀ {{C}}}}
        -> A ⇒ B -> F₀ A ⇒ F₀ B
  _<$>_ = F₁

  open import Data.Nat

  test-→ : (List ℕ -> ℕ) -> (ℕ -> List ℕ) -> ℕ -> ℕ
  test-→ = _<$>_

  test-List : List ℕ
  test-List = ℕ.suc <$> (1 ∷ 2 ∷ 3 ∷ [])
