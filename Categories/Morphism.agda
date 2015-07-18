module Categories.Morphism where

open import Level
open import Function as F using (const; case_of_)
open import Relation.Binary.PropositionalEquality as P
open import Data.Unit
open import Data.Product

open import Categories.Setoid
open import Categories.Category

module _ {α β} {A : Set α} {B : Set β} (f : A -> B)
         {{setoid₁ : Setoid A}} {{setoid₂ : Setoid B}} where
         
  record Injective  : Set (α ⊔ β) where
    field inj  : ∀ {x y} -> f x ≈ f y -> x ≈ y

  record Surjective : Set (α ⊔ β) where
    field surj : ∀ y -> ∃ λ x -> f x ≈ y

  Bijective = Injective × Surjective

module _ {α β} {A : Set α} {B : Set β} {f : A -> B}
         {{setoid₁ : Setoid A}} {{setoid₂ : Setoid B}} where
  instance
    Bijective->Injective  : {{bijective : Bijective f}} -> Injective  f
    Bijective->Injective  {{injective , surjective}} = injective

    Bijective->Surjective : {{bijective : Bijective f}} -> Surjective f
    Bijective->Surjective {{injective , surjective}} = surjective

module _ {α β} {Obj : Set α} {_⇒_ : Obj -> Obj -> Set β}
         {{setoid : ∀ {A B} -> Setoid (A ⇒ B)}} {{C : IsCategory _⇒_}} where
  open IsCategory C

  module _ {A B : Obj} (f : A ⇒ B) where
    record Mono : Set (α ⊔ β) where
      field mono : ∀ {C} {g h : C ⇒ A} -> f ∘ g ≈ f ∘ h -> g ≈ h

    record Epi  : Set (α ⊔ β) where
      field epi  : ∀ {C} {g h : B ⇒ C} -> g ∘ f ≈ h ∘ f -> g ≈ h

    record Iso  : Set (α ⊔ β) where
      field
        f⁻¹  : B ⇒ A
        isoˡ : f ∘ f⁻¹ ≈ id
        isoʳ : f⁻¹ ∘ f ≈ id

  record _≅_ A B : Set (α ⊔ β) where
    field
      {f} : A ⇒ B
      iso : Iso f

record InAgda : Set where
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

  open Injective {{...}}; open Surjective {{...}}
  open Mono {{...}}; open Epi {{...}}; open Iso {{...}}

  infix 9 _⁻¹_
  _⁻¹_ = f⁻¹

  module _ {α} {A B : Set α} {f : A -> B} where
    -- Is not related to Agda.
    Iso->Mono&Epi : {{_ : Iso f}} -> Mono f × Epi f
    Iso->Mono&Epi = record
      { mono = λ {C g h} p x ->
          begin
            g x          ←⟨ isoʳ f (g x)       ⟩
            f ⁻¹ f (g x) →⟨ cong (f⁻¹ f) (p x) ⟩ -- `cong (λ x -> f⁻¹ f x)` gives an error.
            f ⁻¹ f (h x) →⟨ isoʳ f (h x)       ⟩
            h x
          ∎
      }           , record
      { epi  = λ {C g h} p y ->
          begin
            g y            ←⟨ cong g (isoˡ f y) ⟩
            g (f (f ⁻¹ y)) →⟨ p (f ⁻¹ y)        ⟩
            h (f (f ⁻¹ y)) →⟨ cong h (isoˡ f y) ⟩
            h y
          ∎
      }

    Mono->Injective : {{_ : Mono f}} -> Injective f
    Mono->Injective = record { inj = λ p -> mono f (const p) (lift tt) }

    Injective->Mono : {{_ : Injective f}} -> Mono f
    Injective->Mono = record { mono = λ p x -> inj f (p x) }

    -- What is the most constructive way to say this?
    -- Epi->Surjective : {{_ : Epi f}} -> Surjective f

    Surjective->Epi : {{_ : Surjective f}} -> Epi f
    Surjective->Epi = record { epi = λ p y -> uncurry (λ x q -> subst _ q (p x)) (surj f y) }

    Bijective->Iso : {{_ : Bijective f}} -> Iso f
    Bijective->Iso = record
      { f⁻¹  = λ y -> proj₁ (surj f y)
      ; isoˡ = λ y -> proj₂ (surj f y)
      ; isoʳ = λ x -> inj f (proj₂ (surj f (f x)))
      }
