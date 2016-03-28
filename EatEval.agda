-- This is the same as in the "Type theory eating itself?" article
--    http://www.cs.bham.ac.uk/~mhe/TT-perhaps-eating-itself/TT-perhaps-eating-itself.html
-- But we define type checking mutually with evaluation
-- and allow to change the type of a term to a denotationally equal one.

-- This is due to the `coe' constructor.
-- If there would be `Prop' in Agda, we wouldn't need these pragmas.
{-# OPTIONS --type-in-type --universe-polymorphism #-}
-- Alternatively we can remove equality proofs from `coe' and use `trustMe' in ⟦_⟧.

open import Level renaming (zero to lzero; suc to lsuc)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Unit.Base
open import Data.Product

instance
  irefl : ∀ {α} {A : Set α} {x : A} -> x ≡ x
  irefl = refl

infix  4 _⊢_ _⊢*_
infixl 6 _▻_
infixl 8 _[_]ᵗ _[_]

data Con  : Level -> Set
data Type : ∀ {γ} -> Con γ -> Level -> Set
data _⊢*_ : ∀ {γ δ} -> Con δ -> Con γ -> Set
data _⊢_  : ∀ {α γ} -> (Γ : Con γ) -> Type Γ α -> Set

⟦_⟧ᶜ : ∀ {γ} -> Con γ -> Set γ
⟦_⟧ᵗ : ∀ {α γ} {Γ : Con γ} -> Type Γ α -> ⟦ Γ ⟧ᶜ -> Set α
⟦_⟧ˢ : ∀ {γ δ} {Γ : Con γ} {Δ : Con δ} -> Δ ⊢* Γ -> ⟦ Δ ⟧ᶜ -> ⟦ Γ ⟧ᶜ
⟦_⟧  : ∀ {α γ} {Γ : Con γ} {A : Type Γ α} -> Γ ⊢ A -> (ρ : ⟦ Γ ⟧ᶜ) -> ⟦ A ⟧ᵗ ρ

data Con where
  ε   : ∀ {γ} -> Con γ
  _▻_ : ∀ {α γ} -> (Γ : Con γ) -> Type Γ α -> Con (α ⊔ γ)

data Type where
  type  : ∀ {γ} {Γ : Con γ} α -> Type Γ (lsuc α)
  π σ   : ∀ {α β γ} {Γ : Con γ} -> (A : Type Γ α) -> Type (Γ ▻ A) β -> Type Γ (α ⊔ β) 
  ⌈_⌉   : ∀ {α γ} {Γ : Con γ} -> Γ ⊢ type α -> Type Γ α
  _[_]ᵗ : ∀ {α γ δ} {Γ : Con γ} {Δ : Con δ} -> Type Γ α -> Δ ⊢* Γ -> Type Δ α

data _⊢*_ where
  idˢ  : ∀ {γ} {Γ : Con γ} -> Γ ⊢* Γ
  _∘ˢ_ : ∀ {γ δ ξ} {Γ : Con γ} {Δ : Con δ} {Ξ : Con ξ} -> Ξ ⊢* Δ -> Δ ⊢* Γ -> Ξ ⊢* Γ
  _▷_  : ∀ {α γ δ} {Γ : Con γ} {Δ : Con δ} {A : Type Γ α}
       -> (ψ : Δ ⊢* Γ) -> Δ ⊢ A [ ψ ]ᵗ -> Δ ⊢* Γ ▻ A
  ↑    : ∀ {α γ} {Γ : Con γ} {A : Type Γ α} -> Γ ▻ A ⊢* Γ

shiftᵗ : ∀ {α β γ} {Γ : Con γ} {A : Type Γ α} -> Type Γ β -> Type (Γ ▻ A) β
shiftᵗ B = B [ ↑ ]ᵗ

_⟨_⟩ᵗ : ∀ {α β γ} {Γ : Con γ} {A : Type Γ α} -> Type (Γ ▻ A) β -> Γ ⊢ A -> Type Γ β

data _⊢_ where
  vz   : ∀ {α γ} {Γ : Con γ} {A : Type Γ α} -> Γ ▻ A ⊢ shiftᵗ A
  ƛ_   : ∀ {α β γ} {Γ : Con γ} {A : Type Γ α} {B : Type (Γ ▻ A) β}
       -> Γ ▻ A ⊢ B -> Γ ⊢ π A B
  _·_  : ∀ {α β γ} {Γ : Con γ} {A : Type Γ α} {B : Type (Γ ▻ A) β}
       -> Γ ⊢ π A B -> (x : Γ ⊢ A) -> Γ ⊢ B ⟨ x ⟩ᵗ
  pair : ∀ {α β γ} {Γ : Con γ} {A : Type Γ α} {B : Type (Γ ▻ A) β}
       -> (x : Γ ⊢ A) -> Γ ⊢ B ⟨ x ⟩ᵗ -> Γ ⊢ σ A B
  fst  : ∀ {α β γ} {Γ : Con γ} {A : Type Γ α} {B : Type (Γ ▻ A) β}
       -> Γ ⊢ σ A B -> Γ ⊢ A
  snd  : ∀ {α β γ} {Γ : Con γ} {A : Type Γ α} {B : Type (Γ ▻ A) β}
       -> (p : Γ ⊢ σ A B) -> Γ ⊢ B ⟨ fst p ⟩ᵗ
  ⌊_⌋  : ∀ {α γ} {Γ : Con γ} -> Type Γ α -> Γ ⊢ type α
  _[_] : ∀ {α γ δ} {Γ : Con γ} {Δ : Con δ} {A : Type Γ α}
       -> Γ ⊢ A -> (ψ : Δ ⊢* Γ) -> Δ ⊢ A [ ψ ]ᵗ
  coe  : ∀ {α γ} {Γ : Con γ} {A₁ A₂ : Type Γ α}
           {{_ : ∀ {ρ} -> ⟦ A₁ ⟧ᵗ ρ ≡ ⟦ A₂ ⟧ᵗ ρ}}
       -> Γ ⊢ A₁ -> Γ ⊢ A₂

⟦ ε     ⟧ᶜ = Lift ⊤
⟦ Γ ▻ A ⟧ᶜ = Σ ⟦ Γ ⟧ᶜ ⟦ A ⟧ᵗ

⟦ type α   ⟧ᵗ ρ = Set α
⟦ π A B    ⟧ᵗ ρ = (x : ⟦ A ⟧ᵗ ρ) -> ⟦ B ⟧ᵗ (ρ , x)
⟦ σ A B    ⟧ᵗ ρ = Σ (⟦ A ⟧ᵗ ρ) λ x -> ⟦ B ⟧ᵗ (ρ , x) 
⟦ ⌈ t ⌉    ⟧ᵗ ρ = ⟦ t ⟧ ρ
⟦ A [ ψ ]ᵗ ⟧ᵗ ρ = ⟦ A ⟧ᵗ (⟦ ψ ⟧ˢ ρ)

⟦ idˢ    ⟧ˢ ρ = ρ
⟦ φ ∘ˢ ψ ⟧ˢ ρ = ⟦ ψ ⟧ˢ (⟦ φ ⟧ˢ ρ)
⟦ ψ ▷ t  ⟧ˢ ρ = ⟦ ψ ⟧ˢ ρ , (⟦ t ⟧ ρ)
⟦ ↑      ⟧ˢ ρ = proj₁ ρ

B ⟨ x ⟩ᵗ = B [ idˢ ▷ coe x ]ᵗ

⟦ coe {{q}} t ⟧ ρ rewrite sym (q {ρ}) = ⟦ t ⟧ ρ
⟦ vz          ⟧ ρ = proj₂ ρ
⟦ ƛ b         ⟧ ρ = λ x -> ⟦ b ⟧ (ρ , x)
⟦ f · x       ⟧ ρ = ⟦ f ⟧ ρ (⟦ x ⟧ ρ)
⟦ pair t s    ⟧ ρ = ⟦ t ⟧ ρ , ⟦ s ⟧ ρ
⟦ fst p       ⟧ ρ = proj₁ (⟦ p ⟧ ρ)
⟦ snd p       ⟧ ρ = proj₂ (⟦ p ⟧ ρ)
⟦ ⌊ A ⌋       ⟧ ρ = ⟦ A ⟧ᵗ ρ
⟦ t [ ψ ]     ⟧ ρ = ⟦ t ⟧ (⟦ ψ ⟧ˢ ρ)



Type⁺ : Level -> Set
Type⁺ α = ∀ {γ} {Γ : Con γ} -> Type Γ α

Term⁺ : ∀ {α} -> Type⁺ α -> Set
Term⁺ A = ∀ {γ} {Γ : Con γ} -> Γ ⊢ A

_⇒_ : ∀ {α β γ} {Γ : Con γ} -> Type Γ α -> Type Γ β -> Type Γ (α ⊔ β)
A ⇒ B = π A (shiftᵗ B)

⌜_⌝ : ∀ {α γ} {Γ : Con γ} {A : Type Γ (lsuc α)}
        {{_ : ∀ {ρ} -> ⟦ A ⟧ᵗ ρ ≡ ⟦ type α ⟧ᵗ ρ}}
    -> Γ ⊢ A -> Type Γ α
⌜ t ⌝ = ⌈ coe t ⌉

shift : ∀ {α β γ} {Γ : Con γ} {A : Type Γ α} {B : Type Γ β} -> Γ ⊢ A -> Γ ▻ B ⊢ shiftᵗ A
shift t = t [ ↑ ]

vs = shift

I₀ : Term⁺ (π (type lzero) $ ⌜ vz ⌝ ⇒ ⌜ vz ⌝)
I₀ = ƛ ƛ vz

I₁ : Term⁺ (π (type lzero) $ π ⌜ vz ⌝ $ ⌜ vs vz ⌝)
I₁ = ƛ ƛ coe vz

-- To type check this on my machine I place (coe (vs (vs vz))) in a hole and then reify it.
Aᵗ : Type⁺ (lsuc lzero)
Aᵗ = π (type lzero)
   $ π (π ⌜ vz ⌝ $ type lzero)
   $ π (π ⌜ vs vz ⌝ ⌜ (_·_ {B = type lzero} (coe (vs vz)) vz) ⌝)
   $ π ⌜ vs (vs vz) ⌝
   $ ⌜ _·_ {B = type lzero} (coe (vs (vs vz))) vz ⌝
