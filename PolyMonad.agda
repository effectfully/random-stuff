open import Level
open import Function
open import Relation.Binary.PropositionalEquality

record ⊤ α : Set α where
  constructor tt

_<ℓ_ : Level -> Level -> Set
α <ℓ β = suc α ⊔ β ≡ β

Coerce′ : ∀ {α β} -> α ≡ β -> Set α -> Set β
Coerce′ refl = id

coerce′ : ∀ {α β} {A : Set α} -> (q : α ≡ β) -> A -> Coerce′ q A
coerce′ refl = id

record Monad (M : ∀ {α} -> Set α -> Set α) ω : Set ω where
  field
    ret  : ∀ {α} (q : α <ℓ ω) -> Coerce′ q $ ∀ {_ : ⊤ ω} {A : Set α} -> A -> M A
    bind : ∀ {α β} (q : α <ℓ ω) (r : β <ℓ ω)
         -> Coerce′ (cong₂ _⊔_ q r) $
              ∀ {_ : ⊤ ω} {A : Set α} {B : Set β} -> M A -> (A -> M B) -> M B

module Monadic {M : ∀ {α} -> Set α -> Set α} (mMonad : ∀ {ω} -> Monad M ω) where
  infixl 1 _>>=_

  private open module Dummy {ω} = Monad (mMonad {ω})

  return : ∀ {α} {A : Set α} -> A -> M A
  return {α} x = ret {suc α} refl x

  _>>=_ : ∀ {α β} {A : Set α} {B : Set β} -> M A -> (A -> M B) -> M B
  _>>=_ {α} {β} a f = bind {suc (α ⊔ β)} refl refl a f

  join : ∀ {α} {A : Set α} -> M (M A) -> M A
  join = _>>= id
open Monadic {{...}} public

module MakeMonad (M : ∀ {α} -> Set α -> Set α) where
  makeRet : ∀ {α ω}
          -> ({A : Set α} -> A -> M A)
          -> (q : α <ℓ ω)
          -> Coerce′ q $ ∀ {_ : ⊤ ω} {A : Set α} -> A -> M A
  makeRet ret q = coerce′ q λ {_ _} -> ret

  makeBind : ∀ {α β ω}
           -> ({A : Set α} {B : Set β} -> M A -> (A -> M B) -> M B)
           -> (q : α <ℓ ω) (r : β <ℓ ω)
           -> Coerce′ (cong₂ _⊔_ q r) $
                ∀ {_ : ⊤ ω} {A : Set α} {B : Set β} -> M A -> (A -> M B) -> M B
  makeBind bind q r = coerce′ (cong₂ _⊔_ q r) λ {_ _ _} -> bind

private
  module Test where
    open import Data.List.Base

    instance
      ListMonad : ∀ {ω} -> Monad List ω
      ListMonad = record
        { ret  = makeRet  (_∷ [])
        ; bind = makeBind  bind
        } where
            open MakeMonad List

            bind : ∀ {α β} {A : Set α} {B : Set β} -> List A -> (A -> List B) -> List B
            bind  []      f = []
            bind (x ∷ xs) f = f x ++ bind xs f

    -- It should be Applicative, I know.
    mapM : ∀ {α β} {A : Set α} {B : Set β}
             {M : ∀ {α} -> Set α -> Set α} {{mMonad : ∀ {ω} -> Monad M ω}}
         -> (A -> M B) -> List A -> M (List B)
    mapM f  []      = return []
    mapM f (x ∷ xs) = f x >>= λ y -> mapM f xs >>= λ ys -> return (y ∷ ys)

    test₁ : Set -> List Set
    test₁ = return

    test₂ : List Set -> (Set -> List Level) -> (Level -> List Set₂) -> List Set₂
    test₂ xs f g = xs >>= f >>= g

    test₃ : List Set
    test₃ = join $ mapM (const (Level ∷ ⊤ _ ∷ [])) (Set ∷ [])
