module TT.Prelude where

open import Function public
open import Data.Empty public
open import Data.Bool.Base public
open import Data.Nat.Base hiding (erase; _≤_; module _≤_) public
open import Data.Fin hiding (_+_; _<_; _≤_; fold; pred) public
open import Relation.Binary.PropositionalEquality hiding ([_]) public
open import Data.Maybe.Base public
open import Data.Product renaming (map to pmap) public

open import Level using (Lift)
open import Data.Unit.Base
import Data.Fin.Properties as FinProp
import Data.Maybe as Maybe
open import Category.Monad

private open module Dummy {α} = RawMonad {α} Maybe.monad hiding (pure; zipWith) public

From-Maybe : ∀ {α β} {A : Set α} -> (A -> Set β) -> Maybe A -> Set β
From-Maybe B  nothing = Lift ⊤
From-Maybe B (just x) = B x

from-Maybe : ∀ {α β} {A : Set α} {B : A -> Set β} -> (∀ x -> B x) -> (x : Maybe A) -> From-Maybe B x
from-Maybe f  nothing = _
from-Maybe f (just x) = f x

record MEq {α} (A : Set α) : Set α where
  infix 5 _≟_
  field _≟_ : (x y : A) -> Maybe (x ≡ y)
open MEq {{...}} public

instance
  Fin-MEq : ∀ {n} -> MEq (Fin n)
  Fin-MEq = record { _≟_ = λ i j -> decToMaybe (i FinProp.≟ j) }
