-- related to http://stackoverflow.com/questions/31105947/eliminating-a-maybe-at-the-type-level/

open import Level
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Unit.Base
open import Data.Bool
open import Data.Maybe.Base hiding (Is-just) renaming (is-just to isJust)

Is-just : ∀ {α} {A : Set α} -> Maybe A -> Set
Is-just = T ∘ isJust

infixl 1 _>>=ᵗ_
infixl 4 _<$>ᵗ_

data _>>=ᵗ_ {α β} {A : Set α} : (mx : Maybe A) -> (Is-just mx -> Set β) -> Set (α ⊔ β) where
  nothingᵗ : ∀ {B}   ->        nothing >>=ᵗ B
  justᵗ    : ∀ {B x} -> B _ -> just x  >>=ᵗ B

From-justᵗ : ∀ {α β} {A : Set α} {mx : Maybe A} {B : Is-just mx -> Set β}
           -> mx >>=ᵗ B -> Set β
From-justᵗ  nothingᵗ     = Lift ⊤
From-justᵗ (justᵗ {B} y) = B _

from-justᵗ : ∀ {α β} {A : Set α} {mx : Maybe A} {B : Is-just mx -> Set β}
           -> (yᵗ : mx >>=ᵗ B) -> From-justᵗ yᵗ
from-justᵗ  nothingᵗ = _
from-justᵗ (justᵗ y) = y

runᵗ : ∀ {α β} {A : Set α} {mx : Maybe A} {B : Is-just mx -> Set β}
     -> mx >>=ᵗ B -> (imx : Is-just mx) -> B imx
runᵗ {mx = nothing}  _        ()
runᵗ {mx = just  x} (justᵗ y) _  = y

_<$>ᵗ_ : ∀ {α β γ} {A : Set α} {mx : Maybe A} {B : Is-just mx -> Set β} {C : ∀ {x} -> B x -> Set γ}
       -> (∀ {x} -> (y : B x) -> C y) -> (yᵗ : mx >>=ᵗ B) -> mx >>=ᵗ C ∘ runᵗ yᵗ
g <$>ᵗ nothingᵗ = nothingᵗ
g <$>ᵗ justᵗ y  = justᵗ (g y)

! : ∀ {α β} {A : Set α} {B : ∀ {mx} -> Is-just mx -> Set β} {mx : Maybe A}
  -> (∀ x {_ : mx ≡ just x} -> B {just x} _) -> (imx : Is-just mx) -> B imx
! {mx = nothing} f ()
! {mx = just x } f _  = f x {refl}

¡ : ∀ {α β} {A : Set α} {B : A -> Set β} {mx : Maybe A}
  -> (∀ x {_ : mx ≡ just x} -> B x) -> mx >>=ᵗ ! λ x -> B x
¡ {mx = nothing} f = nothingᵗ
¡ {mx = just  x} f = justᵗ (f x {refl})

open import Data.Nat.Base hiding (pred)
open import Data.Vec      hiding (tail)

pred : ℕ -> Maybe ℕ
pred  0      = nothing
pred (suc n) = just n

tailᵗ : ∀ {α n} {A : Set α} -> Vec A n -> pred n >>=ᵗ ! λ pn -> Vec A pn
tailᵗ  []      = nothingᵗ
tailᵗ (x ∷ xs) = justᵗ xs

tail : ∀ {α n} {A : Set α} -> (xs : Vec A n) -> From-justᵗ (tailᵗ xs)
tail = from-justᵗ ∘ tailᵗ

pred-replicate : ∀ {n} -> pred n >>=ᵗ ! λ pn -> Vec ℕ pn
pred-replicate = ¡ λ pn -> replicate {n = pn} 0

test-nil : tail (Vec ℕ 0 ∋ []) ≡ lift tt
test-nil = refl

test-cons : tail (1 ∷ 2 ∷ 3 ∷ []) ≡ 2 ∷ 3 ∷ []
test-cons = refl

test : from-justᵗ ((0 ∷_) <$>ᵗ ((0 ∷_) <$>ᵗ tailᵗ (1 ∷ 2 ∷ 3 ∷ []))) ≡ 0 ∷ 0 ∷ 2 ∷ 3 ∷ []
test = refl

is-just : ∀ {α} {A : Set α} {mx} {x : A} -> mx ≡ just x -> Is-just mx
is-just refl = _

!' : ∀ {α β} {A : Set α} {mx : Maybe A} {B : Is-just mx -> Set β}
   -> (∀ x {p : mx ≡ just x} -> B (is-just p)) -> (imx : Is-just mx) -> B imx
!' {mx = nothing} f ()
!' {mx = just x } f _  = f x {refl}

¡' : ∀ {α β} {A : Set α} {mx : Maybe A} {B : Is-just mx -> Set β}
   -> (∀ x {p : mx ≡ just x} -> B (is-just p)) -> mx >>=ᵗ B
¡' {mx = nothing} f = nothingᵗ
¡' {mx = just  x} f = justᵗ (f x {refl})
