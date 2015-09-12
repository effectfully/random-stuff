-- The idea is due to http://stackoverflow.com/a/26921233/3237465

infix 0 _::_

data _::_ {α} {A : Set α} (x : A) : Set α -> Set α where
  reveal : x :: A

open import Data.Nat.Base
open import Data.Fin hiding (_+_)
open import Data.Nat.Properties.Simple

drop-0 : ∀ n -> (i : Fin (n + 0)) -> i :: Fin n
drop-0 n i rewrite +-right-identity n = reveal
