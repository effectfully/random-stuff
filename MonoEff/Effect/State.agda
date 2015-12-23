module Effect.State where

open import Prelude
open import Core

data State {α} (A : Set α) : Effectful α α α where
  Get : State A A (const A)
  Put : A -> State A ⊤ (const A)

get : ∀ {n α} {Ψs : Effects α α α n} {Rs : Resources α n}
        {A : Set α} {{p : State , A ∈ Ψs , Rs}}
    -> Eff Ψs A Rs _
get = invoke Get

put : ∀ {n α} {Ψs : Effects α α α n} {Rs : Resources α n}
        {A : Set α} {{p : State , A ∈ Ψs , Rs}}
    -> A -> Eff Ψs ⊤ Rs _
put {{p}} = invoke {{p}} ∘ Put

execState : ∀ {n α β} {Ψs : Effects α α α n} {B : Set β}
              {Rs : Resources α (suc n)} {Rs′ : B -> Resources α (suc n)}
          -> head Rs
          -> Eff (State ∷ Ψs)  B                  Rs        Rs′
          -> Eff  Ψs          (Σ B (head ∘ Rs′)) (tail Rs) (tail ∘ Rs′ ∘ proj₁)
execState              s (return y)               = return (y , s)
execState {Rs = _ ∷ _} s (call  zero    Get    f) = execState s (f s)
execState {Rs = _ ∷ _} _ (call  zero   (Put s) f) = execState s (f tt)
execState {Rs = _ ∷ _} s (call (suc i)  a      f) = call i a λ x -> execState s (f x)

open import Data.Bool.Base

eff : Eff (State ∷ State ∷ []) ℕ (ℕ ∷ ⊤ ∷ []) (λ _ -> ℕ ∷ ⊤ ∷ [])
eff = get >>= λ n -> put n >> return (suc n)

-- 4 , 3
test : ℕ × ℕ
test = proj₁ $ runEff $ execState tt $ execState 3 eff
