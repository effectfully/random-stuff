module Categories.Setoid where

open import Level
open import Relation.Binary.PropositionalEquality as P using (_≡_) public
open import Data.Product

record IsEquivalence {α} {A : Set α} (_≈_ : A -> A -> Set α) : Set α where
  field
    refl  : ∀ {x}     -> x ≈ x
    sym   : ∀ {x y}   -> x ≈ y -> y ≈ x
    trans : ∀ {x y z} -> x ≈ y -> y ≈ z -> x ≈ z

module IsEquivalenceOn {α} (A : Set α) where
  private module Dummy = IsEquivalence {A = A}
  open Dummy {{...}} public

-- Arity-generic `IsEquivalenceOn'?
module IsEquivalenceOn₂ {α β} {A : Set α} (_⊕_ : A -> A -> Set β) where
  private module Dummy {x y} = IsEquivalence {A = x ⊕ y}
  open Dummy {{...}} public

record Setoid {α} (A : Set α) : Set (suc α) where
  infix 4 _≈_

  field
    _≈_           : A -> A -> Set α
    isEquivalence : IsEquivalence _≈_
  
  instance
    Setoid->IsEquivalence : IsEquivalence _≈_
    Setoid->IsEquivalence = isEquivalence

record Setoid-Instances : Set where
  open IsEquivalence {{...}}

  postulate
    instance
      Σ-Setoid : ∀ {α β} {A : Set α} {B : A -> Set β}
                   {{setoid₁ : Setoid A}} {setoid₂ : ∀ {x} -> Setoid (B x)}
               -> Setoid (Σ A B)
  instance
-- That's where the idea "_≈_ can't lie in a universe higher than a universe where A lies" fails.
--     →-Setoid : ∀ {α} {A B : Set α} -> Setoid (A -> B)
--     →-Setoid {A} {B} = record
--       { _≈_           = λ f g -> {{setoid : Setoid B}} -> ∀ x -> f x ≈ g x
--       ; isEquivalence = record
--         { refl  = λ     x -> refl
--         ; sym   = λ p   x -> sym   (p x)
--         ; trans = λ p q x -> trans (p x) (q x)
--         }
--       } where open IsEquivalenceOn B

    →-Setoid : ∀ {α} {A B : Set α} {{setoid : Setoid B}} -> Setoid (A -> B)
    →-Setoid {α} {A} {B} {{setoid}} = record
      { _≈_           = λ f g -> ∀ x -> f x ≈ g x
      ; isEquivalence = record
        { refl  = λ     x -> refl
        ; sym   = λ p   x -> sym   (p x)
        ; trans = λ p q x -> trans (p x) (q x)
        }
      } where open Setoid setoid

    ≡-Setoid : ∀ {α} {A : Set α} -> Setoid A
    ≡-Setoid = record
      { _≈_           = _≡_
      ; isEquivalence = record
        { refl  = P.refl
        ; sym   = P.sym
        ; trans = P.trans
        }
      }

module EqReasoning {α} {A : Set α} (setoid : Setoid A) where
  open Setoid setoid; open IsEquivalence isEquivalence

  infix  4 _IsRelatedTo_
  infix  1 begin_
  infixr 2 _→⟨_⟩_ _←⟨_⟩_
  infix  3 _∎
  
  record _IsRelatedTo_ (x y : A) : Set α where
    constructor relTo
    field eq : x ≈ y

  begin_ : ∀ {x y} -> x IsRelatedTo y -> x ≈ y
  begin (relTo p) = p

  _→⟨_⟩_ : ∀ {y z} x -> x ≈ y -> y IsRelatedTo z -> x IsRelatedTo z
  x →⟨ p ⟩ (relTo q) = relTo (trans p q)

  _←⟨_⟩_ : ∀ {y z} x -> y ≈ x -> y IsRelatedTo z -> x IsRelatedTo z
  _←⟨_⟩_ {y} x p (relTo q) = relTo (trans (sym p) q)

  _∎ : ∀ x -> x IsRelatedTo x
  x ∎ = relTo refl
