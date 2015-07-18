module Categories.Functor where

import Function as F
import Relation.Binary.PropositionalEquality as P
open import Data.Product

open import Categories.Category

record IsFunctor
  {α₁ α₂ β₁ β₂} {Obj₁ : Set α₁} {Obj₂ : Set α₂}
  (_⇒₁_ : Obj₁ -> Obj₁ -> Set β₁) (_⇒₂_ : Obj₂ -> Obj₂ -> Set β₂) (F₀ : Obj₁ -> Obj₂)
  {{setoid₁ : ∀ {A B} -> Setoid (A ⇒₁ B)}} {{setoid₂ : ∀ {A B} -> Setoid (A ⇒₂ B)}}
  {{C₁ : IsCategory _⇒₁_}} {{C₂ : IsCategory _⇒₂_}} : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂) where
  open IsCategory {{...}}

  field
    F₁ : ∀ {A B} -> A ⇒₁ B -> F₀ A ⇒₂ F₀ B

    F-id     : ∀ {A} -> F₁ {A} id ≈ id
    F-∘      : ∀ {A B C} {g : B ⇒₁ C} {f : A ⇒₁ B} -> F₁ (g ∘ f) ≈ F₁ g ∘ F₁ f
    F-resp-≈ : ∀ {A B} {f g : A ⇒₁ B} -> f ≈ g -> F₁ f ≈ F₁ g

  isFunctorᵒᵖ : IsFunctor (flip _⇒₁_) (flip _⇒₂_) F₀ {{C₁ = isCategoryᵒᵖ}} {{C₂ = isCategoryᵒᵖ}}
  isFunctorᵒᵖ = record
    { F₁       = F₁
    ; F-id     = F-id
    ; F-∘      = F-∘
    ; F-resp-≈ = F-resp-≈
    }

module Heterogeneousᶠ
  {α₁ α₂ β₁ β₂} {Obj₁ : Set α₁} {Obj₂ : Set α₂}
  {_⇒₁_ : Obj₁ -> Obj₁ -> Set β₁} {_⇒₂_ : Obj₂ -> Obj₂ -> Set β₂} {F₀ : Obj₁ -> Obj₂}
  {{setoid₁ : ∀ {A B} -> Setoid (A ⇒₁ B)}} {{setoid₂ : ∀ {A B} -> Setoid (A ⇒₂ B)}}
  {{C₁ : IsCategory _⇒₁_}} {{C₂ : IsCategory _⇒₂_}} (F : IsFunctor _⇒₁_ _⇒₂_ F₀) where
  open IsFunctor F; open IsCategory {{...}}; open Heterogeneous {{...}}

  hF-id : ∀ {A} -> F₁ {A} id ≋ id
  hF-id = het F-id
  
  hF-∘ : ∀ {A B C} {g : B ⇒₁ C} {f : A ⇒₁ B} -> F₁ (g ∘ f) ≋ F₁ g ∘ F₁ f
  hF-∘ = het F-∘

  F-resp-≋ : ∀ {A A' B B'} {f : A ⇒₁ B} {g : A' ⇒₁ B'} -> f ≋ g -> F₁ f ≋ F₁ g
  F-resp-≋ (het p) = het (F-resp-≈ p)

-- Is it a good practice to always wrap instances in records?
instance
  IsFunctor-Setoid : ∀
    {α₁ α₂ β₁ β₂} {Obj₁ : Set α₁} {Obj₂ : Set α₂}
    {_⇒₁_ : Obj₁ -> Obj₁ -> Set β₁} {_⇒₂_ : Obj₂ -> Obj₂ -> Set β₂} {F₀ : Obj₁ -> Obj₂}
    {{setoid₁ : ∀ {A B} -> Setoid (A ⇒₁ B)}} {{setoid₂ : ∀ {A B} -> Setoid (A ⇒₂ B)}}
    {{C₁ : IsCategory _⇒₁_}} {{C₂ : IsCategory _⇒₂_}}
    -> Setoid (IsFunctor _⇒₁_ _⇒₂_ F₀)
  IsFunctor-Setoid {α₂ = α₂} {_⇒₁_ = _⇒₁_} {_⇒₂_ = _⇒₂_} = record
    { _≈_           = λ Ψ₁ Ψ₂ -> Lift {ℓ = α₂} (∀ {A B} {f : A ⇒₁ B} -> F₁ Ψ₁ f ≈ F₁ Ψ₂ f)
    ; isEquivalence = record
      { refl  =          lift  refl
      ; sym   = λ p   -> lift (sym   (lower p))
      ; trans = λ p q -> lift (trans (lower p) (lower q))
      }
    } where open IsFunctor; open IsEquivalenceOn₂ _⇒₂_

  IsFunctor∀-Setoid : ∀
    {α₁ α₂ β₁ β₂} {Obj₁ : Set α₁} {Obj₂ : Set α₂}
    {_⇒₁_ : Obj₁ -> Obj₁ -> Set β₁} {_⇒₂_ : Obj₂ -> Obj₂ -> Set β₂}
    {{setoid₁ : ∀ {A B} -> Setoid (A ⇒₁ B)}} {{setoid₂ : ∀ {A B} -> Setoid (A ⇒₂ B)}}
    {{C₁ : IsCategory _⇒₁_}} {{C₂ : IsCategory _⇒₂_}}
    -> Setoid (∀ {F₀} -> IsFunctor _⇒₁_ _⇒₂_ F₀)
  IsFunctor∀-Setoid {_⇒₁_ = _⇒₁_} {_⇒₂_ = _⇒₂_} = record
    { _≈_           = λ Ψ₁ Ψ₂ -> ∀ {F₀ A B} {f : A ⇒₁ B} -> F₁ (Ψ₁ {F₀}) f ≈ F₁ (Ψ₂ {F₀}) f
    ; isEquivalence = record
      { refl  =          refl
      ; sym   = λ p   -> sym   p
      ; trans = λ p q -> trans p q
      }
    } where open IsFunctor; open IsEquivalenceOn₂ _⇒₂_

idᶠ : ∀
  {α β} {Obj : Set α} {_⇒_ : Obj -> Obj -> Set β}
  {{setoid : ∀ {A B} -> Setoid (A ⇒ B)}} {{C : IsCategory _⇒_}}
  -> IsFunctor _⇒_ _⇒_ F.id
idᶠ {_⇒_ = _⇒_} = record
  { F₁       = F.id
  ; F-id     = refl
  ; F-∘      = refl
  ; F-resp-≈ = F.id
  } where open IsEquivalenceOn₂ _⇒_

infixr 9 _∘ᶠ_

_∘ᶠ_ : ∀
  {α₁ α₂ α₃ β₁ β₂ β₃} {Obj₁ : Set α₁} {Obj₂ : Set α₂} {Obj₃ : Set α₃}
  {_⇒₁_ : Obj₁ -> Obj₁ -> Set β₁} {{setoid₁ : ∀ {A B} -> Setoid (A ⇒₁ B)}} {{C₁ : IsCategory _⇒₁_}}
  {_⇒₂_ : Obj₂ -> Obj₂ -> Set β₂} {{setoid₂ : ∀ {A B} -> Setoid (A ⇒₂ B)}} {{C₂ : IsCategory _⇒₂_}}
  {_⇒₃_ : Obj₃ -> Obj₃ -> Set β₃} {{setoid₃ : ∀ {A B} -> Setoid (A ⇒₃ B)}} {{C₃ : IsCategory _⇒₃_}}
  {Φ₀ : Obj₂ -> Obj₃} {Ψ₀ : Obj₁ -> Obj₂}
  -> IsFunctor _⇒₂_ _⇒₃_ Φ₀ -> IsFunctor _⇒₁_ _⇒₂_ Ψ₀ -> IsFunctor _⇒₁_ _⇒₃_ (Φ₀ F.∘ Ψ₀)
Φ ∘ᶠ Ψ = record
  { F₁       = F₁ Φ F.∘ F₁ Ψ
  ; F-id     =
      begin
        F₁ Φ (F₁ Ψ id) →⟨ F-resp-≈ Φ (F-id Ψ) ⟩
        F₁ Φ  id       →⟨ F-id Φ              ⟩
        id
      ∎
  ; F-∘      = λ {A} {B} {C} {g} {f} ->
      begin
        F₁ Φ (F₁ Ψ (g ∘ f))           →⟨ F-resp-≈ Φ (F-∘ Ψ) ⟩
        F₁ Φ (F₁ Ψ g ∘ F₁ Ψ f)        →⟨ F-∘ Φ              ⟩
        F₁ Φ (F₁ Ψ g) ∘ F₁ Φ (F₁ Ψ f)
      ∎
  ; F-resp-≈ = F-resp-≈ Φ F.∘ F-resp-≈ Ψ
  } where open IsFunctor; open IsCategory {{...}}

IsEndofunctor : ∀ {α β} {Obj : Set α}
              -> (_⇒_ : Obj -> Obj -> Set β) {{setoid : ∀ {A B} -> Setoid (A ⇒ B)}}
              -> (F₀ : Obj -> Obj) {{isCategory : IsCategory _⇒_}}
              -> Set (α ⊔ β)
IsEndofunctor _⇒_ F₀ = IsFunctor _⇒_ _⇒_ F₀

record Functor {α₁ α₂ β₁ β₂} (C₁ : Category α₁ β₁) (C₂ : Category α₂ β₂)
               : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂) where
  open Category

  field
    {F₀}      : Obj C₁ -> Obj C₂
    isFunctor : IsFunctor _ _ F₀ {{C₁ = isCategory C₁}} {{C₂ = isCategory C₂}}

  instance
    Functor->IsFunctor : IsFunctor _ _ F₀ {{C₁ = isCategory C₁}} {{C₂ = isCategory C₂}}
    Functor->IsFunctor = isFunctor

module HeterogeneousFromᶠ
  {α₁ α₂ β₁ β₂} {C₁ : Category α₁ β₁} {C₂ : Category α₂ β₂} (F : Functor C₁ C₂) where
  open Functor F; open Heterogeneousᶠ isFunctor public

∘ᶠ-assoc : ∀
  {α₁ α₂ α₃ α₄ β₁ β₂ β₃ β₄} {Obj₁ : Set α₁} {Obj₂ : Set α₂} {Obj₃ : Set α₃} {Obj₄ : Set α₄}
  {_⇒₁_ : Obj₁ -> Obj₁ -> Set β₁} {{setoid₁ : ∀ {A B} -> Setoid (A ⇒₁ B)}} {{C₁ : IsCategory _⇒₁_}}
  {_⇒₂_ : Obj₂ -> Obj₂ -> Set β₂} {{setoid₂ : ∀ {A B} -> Setoid (A ⇒₂ B)}} {{C₂ : IsCategory _⇒₂_}}
  {_⇒₃_ : Obj₃ -> Obj₃ -> Set β₃} {{setoid₃ : ∀ {A B} -> Setoid (A ⇒₃ B)}} {{C₃ : IsCategory _⇒₃_}}
  {_⇒₄_ : Obj₄ -> Obj₄ -> Set β₄} {{setoid₄ : ∀ {A B} -> Setoid (A ⇒₄ B)}} {{C₄ : IsCategory _⇒₄_}}
  {Ξ₀ : Obj₃ -> Obj₄} {Φ₀ : Obj₂ -> Obj₃} {Ψ₀ : Obj₁ -> Obj₂}
  (Ξ : IsFunctor _⇒₃_ _⇒₄_ Ξ₀) (Φ : IsFunctor _⇒₂_ _⇒₃_ Φ₀) (Ψ : IsFunctor _⇒₁_ _⇒₂_ Ψ₀)
  -> (Ξ ∘ᶠ Φ) ∘ᶠ Ψ ≈ Ξ ∘ᶠ (Φ ∘ᶠ Ψ)
∘ᶠ-assoc {_⇒₄_ = _⇒₄_} Ξ Φ Ψ = lift refl
  where open IsFunctor; open IsEquivalenceOn₂ _⇒₄_

record Functor-Setoid-Instance : Set where
  -- Hmm... This is just like `IsFunctor-Setoid', but heterogeneous.
  -- Do we have some abstractable pattern here?
  instance
    Functor-Setoid : ∀ {α₁ α₂ β₁ β₂} {C₁ : Category α₁ β₁} {C₂ : Category α₂ β₂}
                   -> Setoid (Functor C₁ C₂)             
    Functor-Setoid {α₂ = α₂} {C₁ = C₁} {C₂ = C₂} = record
      { _≈_           = λ Ψ₁ Ψ₂ -> Lift {ℓ = α₂} (∀ {A B} {f : A ⇒ B} ->
                                                       F₁ (isFunctor Ψ₁) f ≋ F₁ (isFunctor Ψ₂) f)
      ; isEquivalence = record
        { refl  =          lift  hrefl
        ; sym   = λ p   -> lift (hsym   (lower p))
        ; trans = λ p q -> lift (htrans (lower p) (lower q))
        }
      } where open Functor; open IsFunctor; open Category C₁; open HeterogeneousFrom C₂

Endofunctor : ∀ {α β} -> Category α β -> Set (α ⊔ β)
Endofunctor C = Functor C C

record Cat-Instance : Set where
  instance
    Cat : ∀ {α β} -> let open Functor-Setoid-Instance _ in IsCategory (Functor {α₁ = α} {β₁ = β})
    Cat = record
      { id       = record { isFunctor = idᶠ }
      ; _∘_      = λ Φ Ψ -> record { isFunctor = isFunctor Φ ∘ᶠ isFunctor Ψ }
      ; idˡ      = lift hrefl
      ; idʳ      = lift hrefl
      ; assoc    = λ _ -> lift hrefl
      ; ∘-resp-≈ = λ q p -> lift (htrans (lower q) (F-resp-≋ (lower p)))
      } where open Functor; open HeterogeneousFrom {{...}}; open HeterogeneousFromᶠ {{...}}
