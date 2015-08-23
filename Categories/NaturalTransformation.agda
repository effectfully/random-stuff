module Categories.NaturalTransformation where

open import Categories.Category
open import Categories.Functor

-- We could incorporate `η' in the type signature, like in the `IsFunctor' record,
-- but we don't actually care about the function, that performs natural transformation, --
-- just about the fact, that it exists.
record IsNaturalTransformation
  {α₁ α₂ β₁ β₂} {Obj₁ : Set α₁} {Obj₂ : Set α₂}
  {_⇒₁_ : Obj₁ -> Obj₁ -> Set β₁} {_⇒₂_ : Obj₂ -> Obj₂ -> Set β₂}
  {{setoid₁ : ∀ {A B} -> Setoid (A ⇒₁ B)}} {{setoid₂ : ∀ {A B} -> Setoid (A ⇒₂ B)}}
  {{C₁ : IsCategory _⇒₁_}} {{C₂ : IsCategory _⇒₂_}} {Ψ₀ Φ₀ : Obj₁ -> Obj₂}
  (Ψ : IsFunctor _⇒₁_ _⇒₂_ Ψ₀) (Φ : IsFunctor _⇒₁_ _⇒₂_ Φ₀) : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂) where
  open IsFunctor {{...}}; open IsCategory C₂

  field
    η          : ∀ {O} -> Ψ₀ O ⇒₂ Φ₀ O
    naturality : ∀ {A B} {f : A ⇒₁ B} -> η ∘ F₁ f ≈ F₁ f ∘ η

instance
  IsNaturalTransformation-Setoid : ∀
    {α₁ α₂ β₁ β₂} {Obj₁ : Set α₁} {Obj₂ : Set α₂}
    {_⇒₁_ : Obj₁ -> Obj₁ -> Set β₁} {_⇒₂_ : Obj₂ -> Obj₂ -> Set β₂}
    {{setoid₁ : ∀ {A B} -> Setoid (A ⇒₁ B)}} {{setoid₂ : ∀ {A B} -> Setoid (A ⇒₂ B)}}
    {C₁ : IsCategory _⇒₁_} {C₂ : IsCategory _⇒₂_} {Ψ₀ Φ₀ : Obj₁ -> Obj₂}
    {{Ψ : IsFunctor _⇒₁_ _⇒₂_ Ψ₀}} {{Φ : IsFunctor _⇒₁_ _⇒₂_ Φ₀}}
    -> Setoid (IsNaturalTransformation Ψ Φ)
  IsNaturalTransformation-Setoid {α₂ = α₂} {β₁ = β₁} {_⇒₂_ = _⇒₂_} = record
    { _≈_           = λ Η₁ Η₂ -> Lift {ℓ = α₂ ⊔ β₁} (∀ {O} -> η Η₁ {O} ≈ η Η₂ {O})
    ; isEquivalence = record
      { refl  =          lift  refl
      ; sym   = λ p   -> lift (sym   (lower p))
      ; trans = λ p q -> lift (trans (lower p) (lower q))
      }
    } where open IsNaturalTransformation; open IsEquivalenceOn₂ _⇒₂_

idⁿ : ∀
  {α₁ α₂ β₁ β₂} {Obj₁ : Set α₁} {Obj₂ : Set α₂}
  {_⇒₁_ : Obj₁ -> Obj₁ -> Set β₁} {_⇒₂_ : Obj₂ -> Obj₂ -> Set β₂}
  {{setoid₁ : ∀ {A B} -> Setoid (A ⇒₁ B)}} {{setoid₂ : ∀ {A B} -> Setoid (A ⇒₂ B)}}
  {C₁ : IsCategory _⇒₁_} {C₂ : IsCategory _⇒₂_} {Ψ₀ : Obj₁ -> Obj₂} {{Ψ : IsFunctor _⇒₁_ _⇒₂_ Ψ₀}}
  -> IsNaturalTransformation Ψ Ψ
idⁿ {C₂ = C₂} = record
  { η          = λ {O}     -> id
  ; naturality = λ {A B f} ->
      begin
        id ∘ F₁ f →⟨ idˡ ⟩
        F₁ f      ←⟨ idʳ ⟩
        F₁ f ∘ id
      ∎
  } where open IsFunctor {{...}}; open IsCategory C₂

-- Vertical.
_∘ⁿ_ : ∀
  {α₁ α₂ β₁ β₂} {Obj₁ : Set α₁} {Obj₂ : Set α₂}
  {_⇒₁_ : Obj₁ -> Obj₁ -> Set β₁} {_⇒₂_ : Obj₂ -> Obj₂ -> Set β₂}
  {{setoid₁ : ∀ {A B} -> Setoid (A ⇒₁ B)}} {{setoid₂ : ∀ {A B} -> Setoid (A ⇒₂ B)}}
  {C₁ : IsCategory _⇒₁_} {C₂ : IsCategory _⇒₂_} {Ψ₀ Φ₀ Ξ₀ : Obj₁ -> Obj₂}
  {Ψ : IsFunctor _⇒₁_ _⇒₂_ Ψ₀} {Φ : IsFunctor _⇒₁_ _⇒₂_ Φ₀} {Ξ : IsFunctor _⇒₁_ _⇒₂_ Ξ₀}
  -> IsNaturalTransformation Φ Ξ -> IsNaturalTransformation Ψ Φ -> IsNaturalTransformation Ψ Ξ
_∘ⁿ_ {_⇒₂_ = _⇒₂_} {C₂ = C₂} Η₁ Η₂ = record
  { η          = λ {O} -> η Η₁ {O} ∘ η Η₂ {O}
  ; naturality = λ {A B f} ->
      begin
        (η Η₁ ∘ η Η₂) ∘ F₁ f →⟨ assoc (η Η₁)                  ⟩
        η Η₁ ∘ (η Η₂ ∘ F₁ f) →⟨ ∘-resp-≈ refl (naturality Η₂) ⟩
        η Η₁ ∘ (F₁ f ∘ η Η₂) ←⟨ assoc (η Η₁)                  ⟩
        (η Η₁ ∘ F₁ f) ∘ η Η₂ →⟨ ∘-resp-≈ (naturality Η₁) refl ⟩
        (F₁ f ∘ η Η₁) ∘ η Η₂ →⟨ assoc (F₁ f)                  ⟩
        F₁ f ∘ (η Η₁ ∘ η Η₂)
      ∎
  } where open IsNaturalTransformation; open IsFunctor {{...}}
          open IsCategory C₂; open IsEquivalenceOn₂ _⇒₂_

record NaturalTransformation {α₁ α₂ β₁ β₂} {C₁ : Category α₁ β₁} {C₂ : Category α₂ β₂}
                             (Ψ Φ : Functor C₁ C₂) : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂) where
  open Functor

  field
    isNaturalTransformation : IsNaturalTransformation (isFunctor Ψ) (isFunctor Φ)

  instance
    NaturalTransformation->IsNaturalTransformation :
      IsNaturalTransformation (isFunctor Ψ) (isFunctor Φ)
    NaturalTransformation->IsNaturalTransformation = isNaturalTransformation

record NaturalTransformation-Setoid-Instance : Set where
  -- How to express this in terms of `IsNaturalTransformation-Setoid'?
  instance
    NaturalTransformation-Setoid : ∀ {α₁ α₂ β₁ β₂} {C₁ : Category α₁ β₁} {C₂ : Category α₂ β₂}
                                     {Ψ Φ : Functor C₁ C₂} -> Setoid (NaturalTransformation Ψ Φ)
    NaturalTransformation-Setoid {α₂ = α₂} {β₁ = β₁} {C₂ = C₂} = record
      { _≈_           = λ Η₁ Η₂ -> Lift {ℓ = α₂ ⊔ β₁}
                             (∀ {O} ->   η (isNaturalTransformation Η₁) {O}
                                       ≈ η (isNaturalTransformation Η₂) {O})
      ; isEquivalence = record
        { refl  =          lift  refl
        ; sym   = λ p   -> lift (sym   (lower p))
        ; trans = λ p q -> lift (trans (lower p) (lower q))
        }
      } where open NaturalTransformation; open IsNaturalTransformation
              open Category C₂; open IsEquivalenceOn₂ _⇒_
              
record Fun-Instance : Set where
  instance
    Fun : ∀ {α₁ α₂ β₁ β₂} {C₁ : Category α₁ β₁} {C₂ : Category α₂ β₂}
        -> let open NaturalTransformation-Setoid-Instance _ in
             IsCategory {Obj = Functor C₁ C₂} NaturalTransformation
    Fun {C₂ = C₂} = record
      { id       = record { isNaturalTransformation = idⁿ }
      ; _∘_      = λ Η₁ Η₂ -> record { isNaturalTransformation =
                                         isNaturalTransformation Η₁ ∘ⁿ isNaturalTransformation Η₂ }
      ; idˡ      = lift idˡ
      ; idʳ      = lift idʳ
      ; assoc    = λ _ -> lift (assoc _)
      ; ∘-resp-≈ = λ q p -> lift (∘-resp-≈ (lower q) (lower p))
      } where open NaturalTransformation; open IsNaturalTransformation
              open Category C₂; open IsCategory isCategory
