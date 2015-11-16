{-# OPTIONS --no-positivity-check --no-termination-check #-}

module TT.Typecheck where

open import TT.Core

infix  4 _⊢_∈_
infixl 6 _·⁺_

data Value n : Set

ValIsThing : IsThing
ValIsThing = record { Thing = Value }

open IsThing ValIsThing public

data Value n where
  typeᵛ : Value n
  piᵛ   : Value n -> Kripke n -> Value n
  varᵛ  : Fin n -> Value n
  lamᵛ  : Kripke n -> Value n
  _·ᵛ_  : Value n -> Value n -> Value n
  _::ᵛ_ : Value n -> Value n -> Value n

renᵛ : ∀ {n m} -> n ≤ m -> Value n -> Value m
renᵛ ι  typeᵛ    = typeᵛ
renᵛ ι (piᵛ σ k) = piᵛ (renᵛ ι σ) (renᵏ ι k)
renᵛ ι (varᵛ v)  = varᵛ (renᶠ ι v)
renᵛ ι (lamᵛ k)  = lamᵛ (renᵏ ι k)
renᵛ ι (f ·ᵛ x)  = renᵛ ι f ·ᵛ renᵛ ι x
renᵛ ι (x ::ᵛ σ) = renᵛ ι x ::ᵛ renᵛ ι σ

ValCon : Context ValIsThing
ValCon = record { renᵗ = renᵛ }

ValEnv : Environment ValCon
ValEnv = record { fresh = varᵛ zero }

open Context ValCon hiding (renᵗ) public
open module ValEnvironment = Environment ValEnv
-- open ValEnvironment using (apᵏ) public

readback : ∀ {n} -> Value n -> Term n
readback  typeᵛ    = type
readback (piᵛ σ k) = π (readback σ) (readback (apᵏ k))
readback (varᵛ v)  = var v
readback (lamᵛ k)  = ƛ (readback (apᵏ k))
readback (f ·ᵛ x)  = readback f · readback x
readback (x ::ᵛ σ) = readback x :: readback σ

_$ᵛ_ : ∀ {n} -> Value n -> Value n -> Value n
lamᵛ k $ᵛ x = k ·ᵏ x
f      $ᵛ x = f ·ᵛ x

⟦_⟧ : ∀ {n m} -> Term n -> Env m n -> Value m
⟦ type   ⟧ ρ = typeᵛ
⟦ π σ τ  ⟧ ρ = piᵛ (⟦ σ ⟧ ρ) λ ι x -> ⟦ τ ⟧ (renᵉ ι ρ ▷ x)
⟦ var v  ⟧ ρ = lookupᵉ v ρ
⟦ ƛ b    ⟧ ρ = lamᵛ λ ι x -> ⟦ b ⟧ (renᵉ ι ρ ▷ x)
⟦ f · x  ⟧ ρ = ⟦ f ⟧ ρ $ᵛ ⟦ x ⟧ ρ
⟦ x :: σ ⟧ ρ = ⟦ x ⟧ ρ ::ᵛ ⟦ σ ⟧ ρ

eval : ∀ {n} -> Term n -> Value n
eval t = ⟦ t ⟧ stopᵉ

data _⊢_∈_ {n} Γ : Term n -> Value n -> Set where
  type⁺ : Γ ⊢ type ∈ typeᵛ
  π⁺    : ∀ {σ τ} -> Γ ⊢ σ ∈ typeᵛ -> Γ ▻ eval σ ⊢ τ ∈ typeᵛ -> Γ ⊢ π σ τ ∈ typeᵛ
  var⁺  : ∀ v -> Γ ⊢ var v ∈ lookupᶜ v Γ
  ƛ⁺    : ∀ {σ b} {k : Kripke n}
        -> Γ ⊢ erase (readback σ) ∈ typeᵛ -> Γ ▻ σ ⊢ b ∈ apᵏ k -> Γ ⊢ (ƛ b) ∈ piᵛ σ k
  _·⁺_  : ∀ {σ f x} {k : Kripke n} -> Γ ⊢ f ∈ piᵛ σ k -> Γ ⊢ x ∈ σ -> Γ ⊢ f · x ∈ k ·ᵏ eval x

module _ where
  open import Relation.Binary.PropositionalEquality.TrustMe

  coerce : ∀ {n σ τ t} {Γ : Con n} -> Γ ⊢ t ∈ σ -> Maybe (Γ ⊢ t ∈ τ)
  coerce {σ = σ} {τ} t⁺ with readback σ ≟ readback τ
  ... | just  _ rewrite trustMe {x = σ} {y = τ} = just t⁺
  ... | nothing = nothing

mutual
  infer : ∀ {n} (Γ : Con n) t -> Maybe (∃ λ σ -> Γ ⊢ erase t ∈ σ)
  infer Γ  type    = just (, type⁺)
  infer Γ (π σ τ)  = (λ σ⁺ τ⁺ -> , π⁺ σ⁺ τ⁺) <$> check Γ σ typeᵛ ⊛ check (Γ ▻ eval (erase σ)) τ typeᵛ
  infer Γ (var v)  = just (, var⁺ v)
  infer Γ (ƛ b)    = nothing
  infer Γ (f · x)  =
    infer Γ f >>= λ
      { (piᵛ σ k , f⁺) -> (λ x⁺' -> , f⁺ ·⁺ x⁺') <$> check Γ x σ
      ;  _             -> nothing
      }
  infer Γ (x :: σ) = ,_ <$> check Γ x (eval σ)

  check : ∀ {n} (Γ : Con n) t σ -> Maybe (Γ ⊢ erase t ∈ σ)
  check Γ (ƛ b) (piᵛ σ k) = ƛ⁺ <$> check Γ (readback σ) typeᵛ ⊛ check (Γ ▻ σ) b (apᵏ k)
  check Γ  t     σ        = infer Γ t >>= coerce ∘ proj₂

typecheck = from-Maybe proj₂ ∘ infer ε

infixr 4 _Π_
_Π_ : ∀ {n} -> Type n -> Type (suc n) -> Type n
_Π_ = π

Iᵀ = typecheck $ ƛ ƛ var zero :: type Π var zero Π var (suc zero)

Aᵗ : Term⁺
Aᵗ =    type
     Π (var zero Π type)
     Π (var (suc zero) Π var (suc zero) · var zero)
     Π (var (suc (suc zero)))
     Π (var (suc (suc zero)) · var zero)

A : Term⁺
A = ƛ ƛ ƛ ƛ var (suc zero) · var zero :: Aᵗ

Aᵀ = typecheck A

AA : Term⁽⁾
AA = ƛ ƛ A · π (var (suc zero)) (var (suc zero) · var zero)
           · (ƛ (π (var (suc (suc zero))) (var (suc (suc zero)) · var zero)))
           · (A · var (suc zero) · var zero) :: Aᵗ

-- This is where `trustMe` fails: can't unify `ι' with (ι ∘ˡᵉ stop).
AAᵀ = typecheck AA
