module Categories.Category where

open import Level public
open import Function using (flip) public

open import Categories.Setoid public

open Setoid      {{...}} public
open EqReasoning {{...}} public

record IsCategory
  {α β} {Obj : Set α} (_⇒_ : Obj -> Obj -> Set β)
  {{setoid : ∀ {A B} -> Setoid (A ⇒ B)}} : Set (α ⊔ β) where
  infixr 9 _∘_

  field
    id  : ∀ {A}     -> A ⇒ A
    _∘_ : ∀ {A B C} -> B ⇒ C -> A ⇒ B -> A ⇒ C

    idˡ      : ∀ {A B} {f : A ⇒ B} -> id ∘ f ≈ f
    idʳ      : ∀ {A B} {f : A ⇒ B} -> f ∘ id ≈ f
    assoc    : ∀ {A B C D} (h : C ⇒ D) {g : B ⇒ C} {f : A ⇒ B}
             -> (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    ∘-resp-≈ : ∀ {A B C} {g₁ g₂ : B ⇒ C} {f₁ f₂ : A ⇒ B}
             -> g₁ ≈ g₂ -> f₁ ≈ f₂ -> g₁ ∘ f₁ ≈ g₂ ∘ f₂

  open IsEquivalenceOn₂ _⇒_

  isCategoryᵒᵖ : IsCategory (flip _⇒_)
  isCategoryᵒᵖ = record 
    { id       = id
    ; _∘_      = flip _∘_
    ; idˡ      = idʳ
    ; idʳ      = idˡ
    ; assoc    = λ _ -> sym (assoc _)
    ; ∘-resp-≈ = flip ∘-resp-≈
    }

module Heterogeneous
  {α β} {Obj : Set α} {_⇒_ : Obj -> Obj -> Set β}
  {{setoid : ∀ {A B} -> Setoid (A ⇒ B)}} (C : IsCategory _⇒_) where
  open IsCategory C; open IsEquivalenceOn₂ _⇒_

  infix 4 _≋_

  data _≋_ {A B} (f : A ⇒ B) : ∀ {A' B'} -> A' ⇒ B' -> Set β where
    het : ∀ {g} -> f ≈ g -> f ≋ g

  hrefl : ∀ {A B} {f : A ⇒ B}
        -> f ≋ f
  hrefl = het refl

  hsym : ∀ {A A' B B'} {f : A ⇒ B} {g : A' ⇒ B'}
       -> f ≋ g -> g ≋ f
  hsym (het p) = het (sym p)

  htrans : ∀ {A A' A'' B B' B''} {f : A ⇒ B} {g : A' ⇒ B'} {h : A'' ⇒ B''}
         -> f ≋ g -> g ≋ h -> f ≋ h
  htrans (het p) (het q) = het (trans p q)

  ∘-resp-≋ : ∀ {A A' B B' C C'} {g₁ : B ⇒ C} {g₂ : B' ⇒ C'} {f₁ : A ⇒ B} {f₂ : A' ⇒ B'}
           -> g₁ ≋ g₂ -> f₁ ≋ f₂ -> g₁ ∘ f₁ ≋ g₂ ∘ f₂
  ∘-resp-≋ (het p) (het q) = het (∘-resp-≈ p q)

record Category α β : Set (suc (α ⊔ β)) where
  infix  4 _⇒_

  field
    {Obj}      : Set α
    {_⇒_}      : Obj -> Obj -> Set β
    {{setoid}} : ∀ {A B} -> Setoid (A ⇒ B)
    isCategory : IsCategory _⇒_

  instance
    Category->Setoid : ∀ {A B} -> Setoid (A ⇒ B)
    Category->Setoid = setoid

    Category->IsCategory : IsCategory _⇒_
    Category->IsCategory = isCategory

  categoryᵒᵖ : Category α β
  categoryᵒᵖ = record { isCategory = isCategoryᵒᵖ } where open IsCategory isCategory

module IsEquivalenceFrom {α β} (C : Category α β) where
  open Category C; open IsEquivalenceOn₂ _⇒_ public

module HeterogeneousFrom {α β} (C : Category α β) where
  open Category C; open Heterogeneous isCategory public

arr-syntax = Category._⇒_
syntax arr-syntax C A B = A [ C ]⇒ B

eq-syntax : ∀ {α β} -> (C : Category α β) -> ∀ {A B} -> (f g : A [ C ]⇒ B) -> Set β
eq-syntax C f g = f ≈ g where open Category C
syntax eq-syntax C f g = f [ C ]≈ g
