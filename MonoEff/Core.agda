module Core where

open import Prelude

infixl 2 _>>=_
infixr 1 _>>_
infixl 6 _<$>_
infix  3 _∈_

Effectful : ∀ α ρ ε -> Set (lsuc (α ⊔ ρ ⊔ ε))
Effectful α ρ ε = (A : Set α) -> (A -> Set ρ) -> Set ε

Effect : ∀ ρ α ε -> Set (lsuc (ρ ⊔ α ⊔ ε))
Effect ρ α ε = Set ρ -> Effectful α ρ ε

Effects : ∀ ρ α ε -> ℕ -> Set (lsuc (ρ ⊔ α ⊔ ε))
Effects ρ α ε = Vec (Effect ρ α ε)

Resource : ∀ ρ -> Set (lsuc ρ)
Resource ρ = Set ρ

Resources : ∀ ρ -> ℕ -> Set (lsuc ρ)
Resources ρ = Vec (Resource ρ)

data Eff {n ρ α ε β} (Ψs : Effects ρ α ε n) (B : Set β) :
       Resources ρ n -> (B -> Resources ρ n) -> Set (lsuc (ρ ⊔ α) ⊔ β ⊔ ε) where
  return : ∀ {Rs′} y -> Eff Ψs B (Rs′ y) Rs′
  call   : ∀ {A R′ Rs Rs′} i
         -> (a : lookup i Ψs (lookup i Rs) A R′)
         -> (f : ∀ x -> Eff Ψs B (Rs [ i ]≔ R′ x) Rs′)
         -> Eff Ψs B Rs Rs′

runEff : ∀ {ρ α ε β} {B : Set β} -> Eff {0} {ρ} {α} {ε} [] B [] (const []) -> B
runEff (return y)    = y
runEff (call () a f)

_>>=_ : ∀ {n ρ α ε β γ} {Ψs : Effects ρ α ε n} {B : Set β} {C : Set γ}
          {Rs : Resources ρ n} {Rs′ : B -> Resources ρ n} {Rs′′ : C -> Resources ρ n}
      -> Eff Ψs B Rs Rs′ -> (∀ y -> Eff Ψs C (Rs′ y) Rs′′) -> Eff Ψs C Rs Rs′′
return y   >>= g = g y
call i a f >>= g = call i a λ x -> f x >>= g

_>>_ : ∀ {n ρ α ε β γ} {Ψs : Effects ρ α ε n} {B : Set β} {C : Set γ}
         {Rs₁ Rs₂ : Resources ρ n} {Rs′ : C -> Resources ρ n}
     -> Eff Ψs B Rs₁ (const Rs₂) -> Eff Ψs C Rs₂ Rs′ -> Eff Ψs C Rs₁ Rs′
b >> c = b >>= const c

_<$>_ : ∀ {n ρ α ε β γ} {Ψs : Effects ρ α ε n} {B : Set β}
          {Rs₁ Rs₂ : Resources ρ n} {C : Set γ}
      -> (B -> C) -> Eff Ψs B Rs₁ (const Rs₂) -> Eff Ψs C Rs₁ (const Rs₂)
g <$> b = b >>= return ∘ g

_∈_ : ∀ {n ρ α ε}
    -> Effect ρ α ε × Resource ρ -> Effects ρ α ε n × Resources ρ n -> Set (lsuc (ρ ⊔ α ⊔ ε))
_∈_ {0}     (Φ , S) (Ψs     , Rs)     = ⊥
_∈_ {suc n} (Φ , S) (Ψ ∷ Ψs , R ∷ Rs) = Φ ≡ Ψ × S ≡ R ⊎ Φ , S ∈ Ψs , Rs 

∈→Fin : ∀ {n ρ α ε} {ΨR : Effect ρ α ε × Resource ρ} {ΨsRs : Effects ρ α ε n × Resources ρ n}
      -> ΨR ∈ ΨsRs -> Fin n
∈→Fin {0}                            ()
∈→Fin {suc n} {ΨsRs = _ ∷ _ , _ ∷ _} (inj₁ _) = zero
∈→Fin {suc n} {ΨsRs = _ ∷ _ , _ ∷ _} (inj₂ p) = suc (∈→Fin p)

expand : ∀ {n ρ α ε} {Ψ : Effect ρ α ε} {R : Resource ρ} {A : Set α}
           {R′ : A -> Resource ρ} {Ψs : Effects ρ α ε n} {Rs : Resources ρ n}
       -> (p : Ψ , R ∈ Ψs , Rs) -> Ψ R A R′ -> lookup (∈→Fin p) Ψs (lookup (∈→Fin p) Rs) A R′
expand {0}                               ()                   a
expand {suc n} {Ψs = _ ∷ _} {Rs = _ ∷ _} (inj₁ (refl , refl)) a = a 
expand {suc n} {Ψs = _ ∷ _} {Rs = _ ∷ _} (inj₂ p)             a = expand p a

invoke : ∀ {n ρ α ε} {Ψ : Effect ρ α ε} {R : Resource ρ} {A : Set α} {R′ : A -> Resource ρ}
           {Ψs : Effects ρ α ε n} {Rs : Resources ρ n} {{p : Ψ , R ∈ Ψs , Rs}}
       -> Ψ R A R′ -> Eff Ψs A Rs (λ x -> Rs [ ∈→Fin p ]≔ R′ x)
invoke {{p}} a = call (∈→Fin p) (expand p a) return

execEff : ∀ {n ρ α ε β γ} {Ψ : Effect ρ α ε} {Ψs : Effects ρ α ε n} {B : Set β}
            {Rs₁ Rs₂ : Resources ρ (suc n)} {C : B -> Set γ}
        -> (∀ y -> C y)
        -> (∀ {R A R′} -> Ψ R A R′ -> A × ∀ {y} -> C y -> C y)
        -> Eff (Ψ ∷ Ψs)  B       Rs₁       (const Rs₂)
        -> Eff  Ψs      (Σ B C) (tail Rs₁) (tail ∘ const Rs₂)
execEff               ret out (return y)         = return (y , ret y)
execEff {Rs₁ = _ ∷ _} ret out (call  zero   a f) =
  let x , g = out a in second g <$> execEff ret out (f x)
execEff {Rs₁ = _ ∷ _} ret out (call (suc i) a f) = call i a λ x -> execEff ret out (f x)

execEff′ : ∀ {n ρ α ε β γ} {Ψ : Effect ρ α ε} {Ψs : Effects ρ α ε n} {B : Set β}
             {Rs : Resources ρ (suc n)} {Rs′ : B -> Resources ρ (suc n)} {C : B -> Set γ}
         -> (∀ y -> C y)
         -> (∀ {R A R′} -> Ψ R A R′ -> A)
         -> Eff (Ψ ∷ Ψs)  B       Rs        Rs′
         -> Eff  Ψs      (Σ B C) (tail Rs) (tail ∘ Rs′ ∘ proj₁)
execEff′              ret out (return y)         = return (y , ret y)
execEff′ {Rs = _ ∷ _} ret out (call  zero   a f) = execEff′ ret out (f (out a))
execEff′ {Rs = _ ∷ _} ret out (call (suc i) a f) = call i a λ x -> execEff′ ret out (f x)



-- For whatever reason instance search loops if we define _∈_ properly.
-- data _∈_ {ρ α ε} (ΨR : Effect ρ α ε × Resource ρ) :
--        ∀ {n} -> Effects ρ α ε n × Resources ρ n -> Set where
--   here  : ∀ {n Ψs Rs} -> _∈_ ΨR {suc n} (proj₁ ΨR ∷ Ψs , proj₂ ΨR ∷ Rs)
--   there : ∀ {n Φ S Ψs Rs} -> _∈_ ΨR {n} (Ψs , Rs) -> ΨR ∈ Φ ∷ Ψs , S ∷ Rs

-- instance
--   inst-here : ∀ {n ρ α ε} {Ψ : Effect ρ α ε} {R : Resource ρ}
--                 {Ψs : Effects ρ α ε n} {Rs : Resources ρ n}
--             -> Ψ , R ∈ Ψ ∷ Ψs , R ∷ Rs
--   inst-here = here

--   inst-there : ∀ {n ρ α ε} {Ψ : Effect ρ α ε} {R : Resource ρ}
--                  {Ψs : Effects ρ α ε n} {Rs : Resources ρ n}
--                  {Φ S} {{p : Ψ , R ∈ Ψs , Rs}}
--              -> Ψ , R ∈ Φ ∷ Ψs , S ∷ Rs
--   inst-there {{p}} = there p

-- ∈→Fin : ∀ {n ρ α ε} {ΨR : Effect ρ α ε × Resource ρ} {ΨsRs : Effects ρ α ε n × Resources ρ n}
--       -> ΨR ∈ ΨsRs -> Fin n
-- ∈→Fin  here     = zero
-- ∈→Fin (there p) = suc (∈→Fin p)

-- expand : ∀ {n ρ α ε} {Ψ : Effect ρ α ε} {R : Resource ρ} {A : Set α}
--            {R′ : A -> Resource ρ} {Ψs : Effects ρ α ε n} {Rs : Resources ρ n}
--        -> (p : Ψ , R ∈ Ψs , Rs) -> Ψ R A R′ -> lookup (∈→Fin p) Ψs (lookup (∈→Fin p) Rs) A R′
-- expand  here     a = a
-- expand (there p) a = expand p a
