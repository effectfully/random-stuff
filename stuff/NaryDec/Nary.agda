module NaryDec.Nary where

open import Level         renaming (zero to lzero; suc to lsuc) 
open import Function
open import Relation.Nullary
open import Data.Unit.Base
open import Data.Nat.Base hiding (_⊔_)
open import Data.Product  hiding (map)
open import Data.Vec

infixl 6 _^_
infixr 5 _,ʳ_ _,,_ _×ʳ_ _××_
infixr 0 _->ⁿ_

_^_ : ∀ {α} -> Set α -> ℕ -> Set α
A ^ 0     = Lift ⊤
A ^ suc n = A × A ^ n

to-^ : ∀ {n α} {A : Set α} -> Vec A n -> A ^ n
to-^ = foldr (_^_ _) _,_ _

from-^ : ∀ {n α} {A : Set α} -> A ^ n -> Vec A n
from-^ {0}      _       = []
from-^ {suc _} (x , xs) = x ∷ from-^ xs

on-^ : ∀ {α β n} {A : Set α} {B : Vec A n -> Set β}
     -> (∀ xs -> B xs) -> ∀ xs -> B (from-^ xs)
on-^ f = f ∘ from-^

mono-^ : ∀ {α n m} {A : Set α} -> (Vec A n -> Vec A m) -> A ^ n -> A ^ m
mono-^ f = to-^ ∘ on-^ f

_,ʳ_ : ∀ {n α} {A : Set α} -> A ^ n -> A -> A ^ suc n
_,ʳ_ {0}      _       y = y , _
_,ʳ_ {suc _} (x , xs) y = x , xs ,ʳ y

_,,_ : ∀ {n m α} {A : Set α} -> A ^ n -> A ^ m -> A ^ (n + m)
_,,_ {0}      _       ys = ys
_,,_ {suc _} (x , xs) ys = x , xs ,, ys

_⊔ⁿ_ : ∀ {n} -> Level ^ n -> Level -> Level
_⊔ⁿ_ = on-^ $ flip $ foldr _ _⊔_

Sets : ∀ {n} -> (αs : Level ^ n) -> Set (mono-^ (map lsuc) αs ⊔ⁿ lzero)
Sets {0}      _       = ⊤
Sets {suc _} (α , αs) = Σ (Set α) λ A -> A -> Sets αs

_×ʳ_ : ∀ {n β} {αs : Level ^ n} -> Sets αs -> Set β -> Sets (αs ,ʳ β)
_×ʳ_ {0}      _      B = B , _
_×ʳ_ {suc _} (A , F) B = A , λ x -> F x ×ʳ B

_->ⁿ_ : ∀ {n} {αs : Level ^ n} {β} -> Sets αs -> Set β -> Set (αs ⊔ⁿ β)
_->ⁿ_ {0}      _      B = B
_->ⁿ_ {suc _} (_ , F) B = ∀ x -> F x ->ⁿ B

_××_ : ∀ {n m} {αs : Level ^ n} {βs : Level ^ m} -> Sets αs -> Sets βs -> Sets (αs ,, βs)
_××_ {0}      _      Bs = Bs 
_××_ {suc _} (A , F) Bs = A , λ x -> F x ×× Bs

uncurryⁿ : ∀ n {β γ} {αs : Level ^ n} {As : Sets αs} {B : Set β} {C : Set γ}
         -> (As ->ⁿ (B -> C)) -> As ×ʳ B ->ⁿ C
uncurryⁿ  0      f = f
uncurryⁿ (suc n) f = uncurryⁿ n ∘ f

uncurryⁿ² : ∀ n {m γ} {αs : Level ^ n} {βs : Level ^ m}
            {As : Sets αs} {Bs : Sets βs} {C : Set γ}
          -> (As ->ⁿ Bs ->ⁿ C) -> As ×× Bs ->ⁿ C
uncurryⁿ²  0      f = f
uncurryⁿ² (suc n) f = uncurryⁿ² n ∘ f

----------------------------------------

applyⁿ : ∀ n {β γ} {αs : Level ^ n} {As : Sets αs} {B : Set β} {C : B -> Set γ}
       -> (As ->ⁿ ((y : B) -> C y)) -> (y : B) -> As ->ⁿ C y
applyⁿ  0      g y = g y
applyⁿ (suc n) f y = λ x -> applyⁿ n (f x) y

compⁿ : ∀ n {β γ} {αs : Level ^ n} {As : Sets αs} {B : Set β} {C : Set γ}
      -> (B -> C) -> (As ->ⁿ B) -> As ->ⁿ C
compⁿ  0      g y = g y
compⁿ (suc n) g f = compⁿ n g ∘ f

compⁿ² : ∀ m n {β γ} {αs : Level ^ n} {βs : Level ^ m}
         {As : Sets αs} {Bs : Sets βs} {B : Set β} {C : Set γ} 
       -> (Bs ->ⁿ (B -> C)) -> (As ->ⁿ B) -> Bs ×× As ->ⁿ C
compⁿ² m n g f = uncurryⁿ² m $ compⁿ m (λ g' -> compⁿ n g' f) g

∃ⁿ : ∀ n {αs : Level ^ n} {β} {As : Sets αs} -> (As ->ⁿ Set β) -> Set (αs ⊔ⁿ β)
∃ⁿ  0      B = B
∃ⁿ (suc n) F = ∃ (∃ⁿ n ∘ F)
