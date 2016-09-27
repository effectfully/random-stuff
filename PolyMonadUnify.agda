open import Level
open import Function
open import Relation.Binary.PropositionalEquality

record Monad (M : ∀ {α} -> Set α -> Set α) α β : Set (suc (α ⊔ β)) where
  infixl 1 _>>=_

  field
    ret   : {q : α ≡ β} {A : Set α} -> A -> M A
    _>>=_ : {A : Set α} {B : Set β} -> M A -> (A -> M B) -> M B

module Monadic {M : ∀ {α} -> Set α -> Set α} {α} {A : Set α} (mMonad : Monad M α α) where
  private open module Dummy = Monad mMonad

  return : A -> M A
  return = ret {q = refl}

  join : M (M A) -> M A
  join = _>>= id
open Monadic {{...}} public
open Monad   {{...}} using (_>>=_) public

private
  module Test where
    open import Data.List.Base

    instance
      ListMonad : ∀ {α β} -> Monad List α β
      ListMonad = record
        { ret   = _∷ []
        ; _>>=_ = bind
        } where
            bind : ∀ {α β} {A : Set α} {B : Set β} -> List A -> (A -> List B) -> List B
            bind  []      f = []
            bind (x ∷ xs) f = f x ++ bind xs f

    -- It should be Applicative, I know.
    mapM : ∀ {α β} {A : Set α} {B : Set β}
             {M : ∀ {α} -> Set α -> Set α} {{mMonad : ∀ {α β} -> Monad M α β}}
         -> (A -> M B) -> List A -> M (List B)
    mapM f  []      = return []
    mapM f (x ∷ xs) = f x >>= λ y -> mapM f xs >>= λ ys -> return (y ∷ ys)

    test₁ : Set -> List Set
    test₁ = return

    test₂ : List Set -> (Set -> List Level) -> (Level -> List Set₂) -> List Set₂
    test₂ xs f g = xs >>= f >>= g

    test₃ : List Set
    test₃ = join $ mapM (const (Level ∷ List Level ∷ [])) (Set ∷ [])
