module Eff.Freer where

open import Eff.Prelude

infixl 2 _>>=_
infixr 1 _>>_
infixl 5 _<$>_
 
data Freer {α β ψ} (F : Set α -> Set ψ) (B : Set β) : Set (lsuc α ⊔ β ⊔ ψ) where
  return : B -> Freer F B
  call   : ∀ {A} -> F A -> (A -> Freer F B) -> Freer F B

_>>=_ : ∀ {α β γ ψ} {F : Set α -> Set ψ} {B : Set β} {C : Set γ}
      -> Freer F B -> (B -> Freer F C) -> Freer F C
return y >>= g = g y
call a f >>= g = call a λ x -> f x >>= g

_>>_ : ∀ {α β γ ψ} {F : Set α -> Set ψ} {B : Set β} {C : Set γ}
     -> Freer F B -> Freer F C -> Freer F C
b >> c = b >>= const c

_<$>_ : ∀ {α β γ ψ} {F : Set α -> Set ψ} {B : Set β} {C : Set γ}
      -> (B -> C) -> Freer F B -> Freer F C
g <$> b = b >>= return ∘ g

perform : ∀ {α ψ} {F : Set α -> Set ψ} {A : Set α} -> F A -> Freer F A
perform a = call a return
