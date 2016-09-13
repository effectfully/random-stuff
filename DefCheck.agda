open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Maybe.Base hiding (nothing; just; map)
open Maybe
open import Data.List.Base
open import Reflection

infixl 2 _>>=_
infix  5 _≟ᵈ_

pattern explRelArg x = arg (arg-info visible relevant) x

vis : {A : Set} -> (A -> List (Arg Term) -> Term) -> A -> List Term -> Term
vis f x = f x ∘ map explRelArg

vis₀ : {A : Set} -> (A -> List (Arg Term) -> Term) -> A -> Term
vis₀ k x = vis k x []

vis₁ : {A : Set} -> (A -> List (Arg Term) -> Term) -> A -> Term -> Term
vis₁ k f x₁ = vis k f (x₁ ∷ [])

vis₂ : {A : Set} -> (A -> List (Arg Term) -> Term) -> A -> Term -> Term -> Term
vis₂ k f x₁ x₂ = vis k f (x₁ ∷ x₂ ∷ [])

_>>=_ : ∀ {α β} {A : Set α} {B : Set β} -> TC A -> (A -> TC B) -> TC B
_>>=_ = bindTC

_<$>_ : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> TC A -> TC B
f <$> a = a >>= returnTC ∘ f

‵refl : Term
‵refl = vis₀ con (quote refl)

‵nothing : Term
‵nothing = vis₀ con (quote nothing)

‵just : Term -> Term
‵just = vis₁ con (quote just)

_‵≡_ : Term -> Term -> Term
_‵≡_ = vis₂ def (quote _≡_)

‵Maybe : Term -> Term
‵Maybe = vis₁ def (quote Maybe)

macro
  _≟ᵈ_ : ∀ {α} {A : Set α} -> A -> A -> Term -> TC _
  _≟ᵈ_ x y ?r =
    quoteTC x >>= λ qx ->
    quoteTC y >>= λ qy ->
    checkType ?r (‵Maybe (qx ‵≡ qy)) >>= λ ?r′ ->
    catchTC (unify ?r′ (‵just ‵refl)) (unify ?r′ ‵nothing)

open import Data.Nat.Base

test₁ : (2 ∷ 3 ∷ []) ≟ᵈ (2 ∷ 3 ∷ []) ≡ just refl
test₁ = refl

test₂ : (2 ∷ 3 ∷ []) ≟ᵈ (3 ∷ 2 ∷ []) ≡ nothing
test₂ = refl

test₃ : ∀ {α} {A : Set α} {x y z : A} -> (x ∷ y ∷ z ∷ []) ≟ᵈ (x ∷ y ∷ z ∷ []) ≡ just refl
test₃ = refl

test₄ : ∀ {α} {A : Set α} {x y : A} -> x ≟ᵈ y ≡ nothing
test₄ = refl
