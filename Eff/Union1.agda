module Eff.Union1 where

open import Eff.Prelude
open import Eff.Map

-- Sets¹ : ∀ {n} -> (βs : Level ^ n) -> Set _
-- Sets¹ = Map (λ β -> ∀ {α} -> Set α -> Set β)

Sets1 : ∀ {n α} -> Set α -> (βs : Level ^ n) -> Set _
Sets1 A = Map (λ β -> A -> Set β)

Sets¹ : ∀ {n} -> (α : Level) -> (βs : Level ^ n) -> Set _
Sets¹ α = Sets1 (Set α)

Union1 : ∀ {n α} {A : Set α} {βs : Level ^ n} -> Sets1 A βs -> A -> Set _
Union1 Bs x = foldrᵐ Setₛ (λ B R -> B x ⊎ R) ⊥ Bs

inj-replaceᵐ : ∀ n {α β β₀} {βs : Level ^ n} {A : Set α}
                 {B : A -> Set β} {B₀ : A -> Set β₀} {Bs : Sets1 A βs} {x}
             -> (p : B ∈ Bs) -> B₀ x -> Union1 (replaceᵐ (∈→Fin n p) B₀ Bs) x
inj-replaceᵐ  0      () y
inj-replaceᵐ (suc n) (inj₁ r) y = inj₁ y
inj-replaceᵐ (suc n) (inj₂ p) y = inj₂ (inj-replaceᵐ n p y)

-- Make it ((p : B ∈ Bs) -> Union1 Bs x -> B x ⊎ Union1 (deleteᵐ (∈→Fin n p) Bs) x) instead?
popUnion1₀ : ∀ n {α β β₀} {βs : Level ^ n} {A : Set α}
               {B : A -> Set β} {B₀ : A -> Set β₀} {Bs : Sets1 A βs} {x}
           -> (p : B ∈ Bs) -> Union1 Bs x -> B x ⊎ Union1 (replaceᵐ (∈→Fin n p) B₀ Bs) x
popUnion1₀  0       ()       u
popUnion1₀ (suc n) (inj₁ r) (inj₁ y) = inj₁ (hSubst (hsym r) y)
popUnion1₀ (suc n) (inj₁ r) (inj₂ u) = inj₂ (inj₂ u)
popUnion1₀ (suc n) (inj₂ p) (inj₁ y) = inj₂ (inj₁ y)
popUnion1₀ (suc n) (inj₂ p) (inj₂ u) = smap id inj₂ (popUnion1₀ n p u)

popUnion1 : ∀ n {α β β₀} {βs : Level ^ n} {A : Set α}
              {B : A -> Set β} {B₀ : A -> Set β₀} {Bs : Sets1 A βs} {x}
          -> (p : B ∈ Bs) -> Union1 (B₀ , Bs) x -> B x ⊎ Union1 (replaceᵐ (∈→Fin n p) B₀ Bs) x
popUnion1 n p (inj₁ y) = inj₂ (inj-replaceᵐ n p y)
popUnion1 n p (inj₂ u) = popUnion1₀ n p u
