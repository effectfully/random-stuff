-- Based on
-- http://stackoverflow.com/questions/29179508/arity-generic-programming-in-agda
-- http://effectfully.blogspot.com/2016/04/generic-universe-polymorphic.html
-- http://effectfully.blogspot.com/2016/06/deriving-eliminators-of-described-data.html

open import Level renaming (zero to lzero; suc to lsuc)
open import Function
open import Data.Nat.Base hiding (_⊔_)
open import Data.Product

infixl 6 _^_

record Nil {α} : Set α where
  constructor []

_^_ : ∀ {α} -> Set α -> ℕ -> Set α
A ^ 0     = Nil
A ^ suc n = A × A ^ n

foldr : ∀ {n α β} {A : Set α}
      -> (B : ℕ -> Set β) -> (∀ {n} -> A -> B n -> B (suc n)) -> B 0 -> A ^ n -> B n
foldr {0}     B f z  []      = z
foldr {suc n} B f z (x , xs) = f x (foldr B f z xs)

_⊔ⁿ_ : ∀ {n} -> Level ^ n -> Level -> Level
_⊔ⁿ_ = flip $ foldr _ _⊔_

max₀ : ∀ {n} -> Level ^ n -> Level
max₀ = _⊔ⁿ lzero

Tele : ∀ {n} -> (αs : Level ^ n) -> Set (foldr _ (_⊔_ ∘ lsuc) lzero αs)
Tele {0}      []      = Nil
Tele {suc n} (α , αs) = Σ (Set α) λ A -> A -> Tele αs

TList : ∀ {n} {αs : Level ^ n} -> Tele αs -> Set (max₀ αs)
TList {0}      []     = Nil
TList {1}     (A , _) = A
TList {suc n} (A , R) = Σ A λ x -> TList (R x)

Hyp : ∀ {n β} {αs : Level ^ n} -> (As : Tele αs) -> (TList As -> Set β) -> Set (αs ⊔ⁿ β)
Hyp {0}            []     B = B []
Hyp {1}           (A , _) B = (x : A) -> B x 
Hyp {suc (suc n)} (A , R) B = (x : A) -> Hyp (R x) (B ∘ _,_ x)

uncurryⁿ : ∀ n {β} {αs : Level ^ n} {As : Tele αs} {B : TList As -> Set β}
          -> Hyp As B -> ∀ xs -> B xs
uncurryⁿ  0            y  []      = y
uncurryⁿ  1            f  x       = f x
uncurryⁿ (suc (suc n)) f (x , xs) = uncurryⁿ (suc n) (f x) xs

private
  uncurry₀ : ∀ {a b} {A : Set a} {B : A → Set b} → ((x : A) → B x) → (x : A) → B x
  uncurry₀ = uncurryⁿ 1

  uncurry₂ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Σ A B → Set c} →
               ((x : A) → (y : B x) → C (x , y)) →
               ((p : Σ A B) → C p)
  uncurry₂ = uncurryⁿ 2

  uncurry₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c} {D : ∃₂ C → Set d} →
               ((x : A) → (y : B x) → (z : C x y) → D (x , y , z)) →
               ((p : ∃₂ C) → D p)
  uncurry₃ = uncurryⁿ 3
