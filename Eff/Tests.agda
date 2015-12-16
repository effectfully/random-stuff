module Eff.Tests where

open import Eff.Prelude
open import Eff.Freer
open import Eff.Map
open import Eff.Union1
open import Eff.Core

data Reader {α} (A : Set α) : ∀ {β} -> Set β -> Set where
  get : Reader A A

data Writer {α} (A : Set α) : ∀ {β} -> Set β -> Set α where
  put : A -> Writer A {α} ⊤

runReader : ∀ {α β} {A : Set α} {B : Set β} -> A -> Reader A B -> B
runReader x get = x

runWriter : ∀ {α β} {A : Set α} {B : Set β} -> Writer A B -> B × A
runWriter (put x) = _ , x

ask : ∀ {n α} {ψs : Level ^ n} {A : Set α} {Fs : Sets¹ α ψs}
        {{In : Reader A ∈ Fs}} -> Eff Fs A
ask = invoke get

tell : ∀ {n α} {ψs : Level ^ n} {A : Set α} {Fs : Sets¹ α ψs}
         {{In : Writer A ∈ Fs}} -> A -> Eff Fs ⊤
tell = invoke ∘ put

execReader : ∀ {n α β} {ψs : Level ^ n} {A : Set α} {Fs : Sets¹ α ψs} {B : Set β}
           -> A -> Eff (Reader A , Fs) B -> Eff Fs B
execReader x = execEff id id (λ r -> runReader x r , id)

execWriter : ∀ {n α β} {ψs : Level ^ n} {A : Set α} {Fs : Sets¹ α ψs} {B : Set β}
           -> Eff (Writer A , Fs) B -> Eff Fs (List A × B)
execWriter = execEff (List _ ×_) (_,_ []) (second (first ∘ _∷_) ∘ runWriter)



eff₁ : Eff (Writer ℕ , Reader ℕ , tt) ℕ
eff₁ = ask >>= λ n -> tell n >> tell (n + 2) >> return n

eff₂ : Eff (Writer Set , Reader ℕ , tt) ℕ
eff₂ = ask

eff₃ : Eff (Writer Set , Reader ℕ , tt) ℕ
eff₃ = tell (Fin 1) >> return 1

eff₄ : Eff (Writer Set , Reader (Lift {ℓ = lsuc lzero} ℕ) , tt) ℕ
eff₄ = tell (Fin 1) >> ask >>= λ n -> tell (Fin (lower n)) >> return (lower n)

-- 3 ∷ 5 ∷ [] , 3
test₁ : List ℕ × ℕ
test₁ = runEff $ execReader 3 $ execWriter eff₁

-- 3 ∷ 5 ∷ [] , 3
test₂ : List ℕ × ℕ
test₂ = runEff $ execWriter $ execReader 3 $ popEff eff₁
