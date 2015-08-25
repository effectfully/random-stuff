{-# OPTIONS --type-in-type #-}

open import Function
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

record _≃_ (A B : Set) : Set where
  field
    f     : A -> B
    f⁻¹   : B -> A
    .isoˡ : f⁻¹ ∘ f ≗ id
    .isoʳ : f ∘ f⁻¹ ≗ id

record Functor (F : Set -> Set) : Set where
  field
    fmap     : ∀ {A B} -> (A -> B) -> F A -> F B
    .fmap-id : ∀ {A} -> fmap {A} id ≗ id
    .fmap-∘  : ∀ {A B C} {g : B -> C} {f : A -> B} -> fmap (g ∘ f) ≗ fmap g ∘ fmap f 

module Parametricity where
  module _  {F : Set -> Set} (Ψ : Functor F) where
    open Functor Ψ

    postulate
      isoˡ : ∀ {A}
           -> (η : ∀ {B} -> (A -> B) -> F B)
           -> (λ {B} (f : A -> B) -> fmap f (η id)) ≡ η

  Yoneda : ∀ {F : Set -> Set} {A}
          -> Functor F -> (∀ {B} -> (A -> B) -> F B) ≃ F A
  Yoneda {A = A} Ψ = record
    { f    = _$ id
    ; f⁻¹  = λ x f -> fmap f x
    ; isoˡ = isoˡ Ψ
    ; isoʳ = fmap-id
    } where open Functor Ψ

-- natural trasformations
record _∸>_ {F₁ F₂} (Ψ₁ : Functor F₁) (Ψ₂ : Functor F₂) : Set where
  constructor Nat
  
  open Functor

  field
    η           : ∀ A -> F₁ A -> F₂ A
    .naturality : ∀ {A B} {f : A -> B} -> η B ∘ fmap Ψ₁ f ≗ fmap Ψ₂ f ∘ η A

module _ where
  open _∸>_

  η-rule : ∀ {F₁ F₂} {Ψ₁ : Functor F₁} {Ψ₂ : Functor F₂} {N₁ N₂ : Ψ₁ ∸> Ψ₂}
         -> η N₁ ≡ η N₂ -> N₁ ≡ N₂
  η-rule refl = refl

-- covariant hom-functor
~> : ∀ A -> Functor (λ B -> A -> B)
~> A = record
  { fmap    = λ g f -> g ∘ f
  ; fmap-id = λ x -> refl
  ; fmap-∘  = λ x -> refl
  }

postulate
  ext : ∀ {α β} -> Extensionality α β

Yoneda : ∀ {F : Set -> Set} {A} -> (Ψ : Functor F) -> ((~>) A ∸> Ψ) ≃ F A
Yoneda {A = A} Ψ = record
  { f    = λ N -> η N A id
  ; f⁻¹  = λ ⌜x⌝ -> record
      { η          = λ B f -> fmap f ⌜x⌝
      ; naturality = λ f   -> fmap-∘ ⌜x⌝
      }
  ; isoˡ = λ N -> η-rule $ ext λ B -> ext λ f -> sym (naturality N id)
  ; isoʳ = fmap-id
  } where open _∸>_; open Functor Ψ
