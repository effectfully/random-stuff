module Eff.Core where

open import Eff.Prelude
open import Eff.Freer
open import Eff.Map
open import Eff.Union1

-- Tagging to make implicits inferrable.
-- We could define a wrapper over `Freer',
-- but that would introduce too much wrapping-unwrapping boilerplate.
Eff : ∀ {n α γ} {ψs : Level ^ n} -> Sets¹ α ψs -> Set γ -> Set _
Eff Fs = Freer (Tag₂ Union1 Fs)

pattern tcall a f = call (tag a) f 

inj : ∀ n {α ψ} {ψs : Level ^ n} {A : Set α} {F : Set α -> Set ψ} {Fs : Sets¹ α ψs}
    -> F A -> F ∈ Fs -> Union1 Fs A
inj  0      a  ()
inj (suc n) a (inj₁ r) = inj₁ (hSubst r a)
inj (suc n) a (inj₂ p) = inj₂ (inj n a p)

invoke : ∀ {n α ψ} {ψs : Level ^ n} {A : Set α} {F : Set α -> Set ψ}
           {Fs : Sets¹ α ψs} {{p : F ∈ Fs}}
       -> F A -> Eff Fs A
invoke {n} {{p}} a = perform (tag (inj n a p))

execEff : ∀ {n α β ψ φ} {ψs : Level ^ n} {F : Set α -> Set ψ}
            {Fs : Sets¹ α ψs} {B : Set β}
        -> (G : Set β -> Set φ)
        -> (B -> G B)
        -> (∀ {A} -> F A -> A × (G B -> G B))
        -> Eff (F , Fs) B
        -> Eff Fs (G B)
execEff G ret out (return y)         = return (ret y)
execEff G ret out (tcall (inj₁ a) f) = let x , g = out a in g <$> execEff G ret out (f x)
execEff G ret out (tcall (inj₂ a) f) = tcall a λ x -> execEff G ret out (f x)

runEff : ∀ {α β} {B : Set β} -> Eff {α = α} tt B -> B
runEff (return y)   = y
runEff (tcall () _)

popEff : ∀ {n α β ψ ψ₀} {ψs : Level ^ n} {B : Set β}
           {F : Set α -> Set ψ} {F₀ : Set α -> Set ψ₀}
           {Fs : Sets¹ α ψs} {{p : F ∈ Fs}}
       -> Eff (F₀ , Fs) B -> Eff {ψs = ψ , _} (F , replaceᵐ (∈→Fin n p) F₀ Fs) B
popEff           (return y)  = return y
popEff {n} {{p}} (tcall a f) = tcall (popUnion1 n p a) λ x -> popEff (f x)
