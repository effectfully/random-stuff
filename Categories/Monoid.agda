module Categories.Monoid where

import Function as F
open import Data.Unit

open import Categories.Category
open import Categories.Functor

record Monoid {α} (A : Set α) {{setoid : Setoid A}} : Set α where
  infix 5 _∙_

  field
    ε   : A
    _∙_ : A -> A -> A

    idˡ      : ∀ {x} -> ε ∙ x ≈ x
    idʳ      : ∀ {x} -> x ∙ ε ≈ x
    assoc    : ∀ {x y z} -> (x ∙ y) ∙ z ≈ x ∙ (y ∙ z)
    ∙-resp-≈ : ∀ {x₁ x₂ y₁ y₂} -> x₁ ≈ x₂ -> y₁ ≈ y₂ -> x₁ ∙ y₁ ≈ x₂ ∙ y₂

record MonoidHom {α β} {A : Set α} {B : Set β} {{setoid₁ : Setoid A}} {{setoid₂ : Setoid B}}
                 (M₁ : Monoid A) (M₂ : Monoid B) : Set (α ⊔ β) where
  open Monoid {{...}}

  field
    f₁ : A -> B

    f-ε      : f₁ ε ≈ ε
    f-∙      : ∀ {x y} -> f₁ (x ∙ y) ≈ f₁ x ∙ f₁ y
    f-resp-≈ : ∀ {x y} -> x ≈ y -> f₁ x ≈ f₁ y

idʰ : ∀ {α} {A : Set α} {{setoid : Setoid A}} {M : Monoid A} -> MonoidHom M M
idʰ {A = A} = record
  { f₁       = F.id
  ; f-ε      = refl
  ; f-∙      = refl
  ; f-resp-≈ = F.id
  } where open IsEquivalenceOn A

-- Can we derive this from the fact, that monoid homomorphisms are functors? Should we?
_∘ʰ_ : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ}
         {{setoid₁ : Setoid A}} {{setoid₂ : Setoid B}} {{setoid₃ : Setoid C}}
         {M₁ : Monoid A} {M₂ : Monoid B} {M₃ : Monoid C}
     -> MonoidHom M₂ M₃ -> MonoidHom M₁ M₂ -> MonoidHom M₁ M₃
_∘ʰ_ {C = C} H₁ H₂ = record
  { f₁       = f₁ H₁ F.∘ f₁ H₂
  ; f-ε      =
      begin
        f₁ H₁ (f₁ H₂ ε) →⟨ f-resp-≈ H₁ (f-ε H₂) ⟩
        f₁ H₁  ε        →⟨ f-ε H₁ ⟩
        ε
      ∎
  ; f-∙      = λ {x y} ->
      begin
        f₁ H₁ (f₁ H₂ (x ∙ y))             →⟨ f-resp-≈ H₁ (f-∙ H₂) ⟩
        f₁ H₁ (f₁ H₂ x ∙ f₁ H₂ y)         →⟨ f-∙ H₁ ⟩
        f₁ H₁ (f₁ H₂ x) ∙ f₁ H₁ (f₁ H₂ y)
      ∎
  ; f-resp-≈ = f-resp-≈ H₁ F.∘ f-resp-≈ H₂
  } where open MonoidHom; open Monoid {{...}}; open IsEquivalenceOn C

instance
  MonoidHom-Setoid : ∀ {α β} {A : Set α} {B : Set β} {{setoid₁ : Setoid A}} {{setoid₂ : Setoid B}}
                       {{M₁ : Monoid A}} {{M₂ : Monoid B}}
                   -> Setoid (MonoidHom M₁ M₂)
  MonoidHom-Setoid {B = B} = record
    { _≈_           = λ H₁ H₂ -> ∀ {x} -> f₁ H₁ x ≈ f₁ H₂ x
    ; isEquivalence = record
      { refl  = refl
      ; sym   = λ p   -> sym p
      ; trans = λ p q -> trans p q
      }
    } where open MonoidHom; open IsEquivalenceOn B

  Mon : ∀ {α} {A : Set α} {{setoid : Setoid A}} -> IsCategory {Obj = Monoid A} MonoidHom
  Mon {A = A} = record
    { id       = idʰ
    ; _∘_      = _∘ʰ_
    ; idˡ      = refl
    ; idʳ      = refl
    ; assoc    = refl
    ; ∘-resp-≈ = λ {M₁ M₂ M₃ H₁ H₂ H₃ H₄} q p -> trans q (f-resp-≈ H₂ p)
    } where open MonoidHom; open IsEquivalenceOn A

  Monoid-IsCategory : ∀ {α} {A : Set α} {{setoid : Setoid A}} {{M : Monoid A}}
                      -> IsCategory {Obj = ⊤} (λ _ _ -> A)
  Monoid-IsCategory {{M = M}} = record
    { id       = ε
    ; _∘_      = _∙_
    ; idˡ      = idˡ
    ; idʳ      = idʳ
    ; assoc    = assoc
    ; ∘-resp-≈ = ∙-resp-≈
    } where open Monoid M

  MonoidHom-IsFunctor : ∀
    {α β} {A : Set α} {B : Set β} {{setoid₁ : Setoid A}} {{setoid₂ : Setoid B}}
    {M₁ : Monoid A} {M₂ : Monoid B} {{H : MonoidHom M₁ M₂}}
    -> IsFunctor (λ _ _ -> A) (λ _ _ -> B) F.id
  MonoidHom-IsFunctor {{H = H}} = record
    { F₁       = f₁
    ; F-id     = f-ε
    ; F-∘      = f-∙
    ; F-resp-≈ = f-resp-≈
    } where open MonoidHom H
