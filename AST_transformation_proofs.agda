-- This is related to http://stackoverflow.com/questions/24475546/non-tedious-ast-transformation-proofs-in-agda/

{-# OPTIONS --rewriting #-}

module AST_transformation_proofs where

open import Level
open import Function
open import Relation.Nullary hiding (Dec)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Bool
open import Data.Product hiding (map)
open import Data.Nat hiding (_⊔_)
open import Data.Maybe as M hiding (map)
open import Data.Maybe.Categorical as M
import Data.List as L
import Data.List.Categorical as L
open import Data.Vec hiding (_⊛_)
open import Category.Monad

-- Misc

neighbWith : {α β : Level} {A : Set α} {B : Set β} -> (A -> A -> B) -> L.List A -> L.List B
neighbWith f xs = L.zipWith f xs (L.drop 1 xs)

private
  module Monadic {m} {M : Set m → Set m} (Mon : RawMonad M) where
    open RawMonad Mon

    sequence : ∀ {A n} → Vec (M A) n → M (Vec A n)
    sequence []       = return []
    sequence (x ∷ xs) = _∷_ <$> x ⊛ sequence xs

    mapM : ∀ {a} {A : Set a} {B n} → (A → M B) → Vec A n → M (Vec B n)
    mapM f = sequence ∘ map f

open Monadic public

lhead : {α : Level} {A : Set α} -> A -> L.List A -> A
lhead z  L.[]     = z
lhead z (x L.∷ _) = x

-- Decidability

data Dec' {p} (P : Set p) : Set p where
  yes' : (p : P) → Dec' P
  no'  : Dec' P

dec'ToMaybe⊤ : ∀ {a} {A : Set a} → Dec' A → Maybe ⊤
dec'ToMaybe⊤ (yes' x) = just _
dec'ToMaybe⊤  no'     = nothing

Decidable' : ∀ {a b ℓ} {A : Set a} {B : Set b} → REL A B ℓ → Set _
Decidable' _∼_ = ∀ x y → Dec' (x ∼ y)

-- nary

naryLevel : ℕ -> Level -> Level -> Level
naryLevel n α γ = L.foldr _⊔_ γ $ L.replicate n α

nary : {α γ : Level} -> (n : ℕ) -> Set α -> Set γ -> Set (naryLevel n α γ)
nary  0      X Z = Z
nary (suc n) X Z = X -> nary n X Z

naryApply : {α γ : Level} {X : Set α} {Z : Set γ} -> (n : ℕ) -> nary n X Z -> X -> Z
naryApply  0      x _ = x
naryApply (suc n) f x = naryApply n (f x) x

naryApplyWith : {α γ : Level} {X : Set α} {Z : Set γ}
              -> (n : ℕ) -> nary n X Z -> (X -> X) -> X -> Z
naryApplyWith  0      x _ _ = x
naryApplyWith (suc n) f g x = naryApplyWith n (f x) g (g x)

-- Subterms

transT : {α : Level} -> Set α -> Set α
transT A = A -> A

transTs : {α : Level} -> Set α -> Set α
transTs A = L.List (transT A)

transTss : {α : Level} -> Set α -> ℕ -> Set α
transTss A l = Vec (transTs A) l

record Proving {α β : Level} (A : Set α) (B : Set β) : Set (α ⊔ β) where
  constructor all
  field
    transform  : (A -> A) -> A -> A
    _≟A_       : Decidable' {A = A} _≡_
    directions : A -> A -> transTs A
    size       : A -> ℕ
    enlarge    : A -> A
    small      : A
    meaning    : A -> B
    generalize : ∀ f -> (∀ e -> meaning (f e) ≡ meaning e)
               -> ∀ e -> meaning (transform f e) ≡ meaning e

add : {α : Level} {A : Set α} {l : ℕ} -> ℕ -> transT A -> transTss A l -> transTss A l
add  _      d  []      = []
add  0      d (x ∷ xs) = (d L.∷ x) ∷ xs
add (suc n) d (x ∷ xs) = x ∷ add n d xs

directionses : {α β : Level} {A : Set α} {B : Set β}
             -> Proving A B -> (n : ℕ) -> nary n A (A × A) -> transTss A n
directionses pr n f =
  L.foldr (λ f -> add (size (f e)) f) (replicate L.[]) $
    directions (proj₁ $ naryApply n f (enlarge small)) (proj₁ $ naryApply n f small) where
      open Proving pr
      e = proj₁ $ naryApplyWith n f enlarge small

open RawMonad {{...}}

getSubterms : {α β : Level} {A : Set α} {B : Set β}
            -> Proving A B -> (n : ℕ) -> nary n A (A × A) -> A -> Maybe (Vec A n)
getSubterms pr n f e
    with directionses pr n f
... | dss with flip (mapM M.monad) dss
      (L.TraversableM.sequenceM M.monad ∘ neighbWith (λ f g -> dec'ToMaybe⊤ $ Proving._≟A_ pr (f e) (g e)))
... | nothing = nothing
... | just _  = just (map (λ fs -> lhead id fs e) dss)

-- Transforming

vecApply : {α γ : Level} {X : Set α} {Z : Set γ} -> (n : ℕ) -> nary n X Z -> Vec X n -> Z
vecApply  0      x  _       = x
vecApply (suc n) f (x ∷ xs) = vecApply n (f x) xs

replace' : {α β : Level} {A : Set α} {B : Set β}
         -> Proving A B -> (n : ℕ) -> nary n A (A × A) -> A -> A
replace' pr n f e with getSubterms pr n f e
replace' pr n f e | nothing = e
replace' pr n f e | just xs with vecApply n f xs
replace' pr n f e | just xs |  e' , e'' with Proving._≟A_ pr e e'
replace' pr n f e | just xs |  e' , e'' | no'       = e
replace' pr n f e | just xs | .e  , e'' | yes' refl = e''

replace : {α β : Level} {A : Set α} {B : Set β}
        -> Proving A B -> (n : ℕ) -> nary n A (A × A) -> A -> A
replace pr n f = Proving.transform pr (replace' pr n f)

-- Proving

soundnessProof : {α β : Level} {A : Set α} {B : Set β}
               -> Proving A B -> (n : ℕ) -> nary n A (A × A) -> Set (naryLevel n α β)
soundnessProof pr  0      (e' , e'') = meaning e' ≡ meaning e'' where open Proving pr
soundnessProof pr (suc n)     f      = ∀ x -> soundnessProof pr n (f x)

vecApplyProof : {α β : Level} {A : Set α} {B : Set β} {n : ℕ} {f : nary n A (A × A)}
              -> (pr : Proving A B) -> soundnessProof pr n f -> (xs : Vec A n)
              -> let open Proving pr
                 in uncurry (λ p1 p2 -> meaning p1 ≡ meaning p2) $ vecApply n f xs
vecApplyProof {n = 0}     pr p  _       = p
vecApplyProof {n = suc n} pr p (x ∷ xs) = vecApplyProof {n = n} pr (p x) xs

sound' : {α β : Level} {A : Set α} {B : Set β}
       -> (pr : Proving A B) -> (n : ℕ) -> (f : nary n A (A × A)) -> soundnessProof pr n f
       -> ∀ e -> let open Proving pr
                 in meaning (replace' pr n f e) ≡ meaning e
sound' pr n f p e with getSubterms pr n f e
sound' pr n f p e | nothing = refl
sound' pr n f p e | just xs with vecApply n f xs | vecApplyProof pr p xs
sound' pr n f p e | just xs |  e' , e'' | p' with Proving._≟A_ pr e e'
sound' pr n f p e | just xs |  e' , e'' | p' | no'       = refl
sound' pr n f p e | just xs | .e  , e'' | p' | yes' refl = sym p'

sound : {α β : Level} {A : Set α} {B : Set β}
      -> (pr : Proving A B) -> (n : ℕ) -> (f : nary n A (A × A)) -> soundnessProof pr n f
      -> ∀ e -> let open Proving pr
                in meaning (replace pr n f e) ≡ meaning e
sound pr n f p = Proving.generalize pr _ (sound' pr n f p)

-- Nicety

_==_ : {α β : Level} {A : Set α} {B : Set β} -> A -> B -> A × B
_==_ = _,_

-- AExp

data AExp : Set where
  ANum : ℕ → AExp
  APlus AMinus AMult : AExp → AExp → AExp

aeval : AExp → ℕ
aeval (ANum   x)   = x
aeval (APlus  a b) = aeval a + aeval b
aeval (AMinus a b) = aeval a ∸ aeval b
aeval (AMult  a b) = aeval a * aeval b

_≟AExp_ : Decidable' {A = AExp} _≡_
ANum   x     ≟AExp ANum    y      with x Data.Nat.≟ y
ANum   x     ≟AExp ANum    y      | no  _    = no'
ANum   x     ≟AExp ANum   .x      | yes refl = yes' refl
APlus  e1 e2 ≟AExp APlus   e3  e4 with e1 ≟AExp e3
APlus  e1 e2 ≟AExp APlus   e3  e4 | no'       = no'
APlus  e1 e2 ≟AExp APlus  .e1  e4 | yes' refl with e2 ≟AExp e4
APlus  e1 e2 ≟AExp APlus  .e1  e4 | yes' refl | no'       = no'
APlus  e1 e2 ≟AExp APlus  .e1 .e2 | yes' refl | yes' refl = yes' refl
AMinus e1 e2 ≟AExp AMinus  e3  e4 with e1 ≟AExp e3
AMinus e1 e2 ≟AExp AMinus  e3  e4 | no'       = no'
AMinus e1 e2 ≟AExp AMinus .e1  e4 | yes' refl with e2 ≟AExp e4
AMinus e1 e2 ≟AExp AMinus .e1  e4 | yes' refl | no'       = no'
AMinus e1 e2 ≟AExp AMinus .e1 .e2 | yes' refl | yes' refl = yes' refl
AMult  e1 e2 ≟AExp AMult   e3  e4 with e1 ≟AExp e3
AMult  e1 e2 ≟AExp AMult   e3  e4 | no'       = no'
AMult  e1 e2 ≟AExp AMult  .e1  e4 | yes' refl with e2 ≟AExp e4
AMult  e1 e2 ≟AExp AMult  .e1  e4 | yes' refl | no'       = no'
AMult  e1 e2 ≟AExp AMult  .e1 .e2 | yes' refl | yes' refl = yes' refl
_            ≟AExp _              = no'

transform : (AExp → AExp) → AExp → AExp
transform f (ANum x)     = f (ANum x)
transform f (APlus a b)  = f (APlus  (transform f a) (transform f b))
transform f (AMinus a b) = f (AMinus (transform f a) (transform f b))
transform f (AMult a b)  = f (AMult  (transform f a) (transform f b))

left : transT AExp
left (ANum   x  ) = ANum x
left (APlus  a b) = a
left (AMinus a b) = a
left (AMult  a b) = a

right : transT AExp
right (ANum   x  ) = ANum x
right (APlus  a b) = b
right (AMinus a b) = b
right (AMult  a b) = b

directions : AExp -> AExp -> transTs AExp
directions (ANum   _)     (ANum   _)     = L.[]
directions (APlus  a1 a2) (APlus  b1 b2) =
  L.map (λ f -> f ∘ left) (directions a1 b1) L.++ L.map (λ f -> f ∘ right) (directions a2 b2)
directions (AMinus a1 a2) (AMinus b1 b2) =
  L.map (λ f -> f ∘ left) (directions a1 b1) L.++ L.map (λ f -> f ∘ right) (directions a2 b2)
directions (AMult  a1 a2) (AMult  b1 b2) =
  L.map (λ f -> f ∘ left) (directions a1 b1) L.++ L.map (λ f -> f ∘ right) (directions a2 b2)
directions  _              _             = id L.∷ L.[]

size : AExp -> ℕ
size (APlus a _) = 1 + size a
size  _          = 0

generalize : ∀ f -> (∀ e -> aeval (f e) ≡ aeval e)
           -> (∀ e -> aeval (transform f e) ≡ aeval e)
generalize f p (ANum x)     = p (ANum x)
generalize f p (APlus a b)  rewrite p (APlus  (transform f a) (transform f b))
  | generalize f p a | generalize f p b = refl
generalize f p (AMinus a b) rewrite p (AMinus (transform f a) (transform f b))
  | generalize f p a | generalize f p b = refl
generalize f p (AMult a b)  rewrite p (AMult  (transform f a) (transform f b))
  | generalize f p a | generalize f p b = refl

AExpPr : Proving AExp ℕ
AExpPr = all transform _≟AExp_ directions size (λ a -> APlus a a) (ANum 0) aeval generalize

-- Example 1

ex1-func : (_ _ : AExp) -> AExp × AExp
ex1-func = λ a1 b1 -> AMult (APlus a1 b1) (APlus a1 b1) == ANum 0

opt-ex1-func : AExp → AExp
opt-ex1-func = replace AExpPr 2 ex1-func

test-ex1-func :
  let    a1 = ANum 0
  in let b1 = ANum 1
  in opt-ex1-func (AMinus (AMult (APlus a1 b1) (APlus a1 b1)) (ANum 0)) ≡ AMinus (ANum 0) (ANum 0)
test-ex1-func = refl

-- Example 2

0+-func : AExp -> AExp × AExp
0+-func = λ a2 -> APlus (ANum 0) a2 == a2

opt-0+ : AExp → AExp
opt-0+ = replace AExpPr 1 0+-func

test-opt-0+ : opt-0+ (AMult (APlus (ANum 0) (ANum 1)) (ANum 2)) ≡ AMult (ANum 1) (ANum 2)
test-opt-0+ = refl

opt-0+-sound : ∀ e → aeval (opt-0+ e) ≡ aeval e
opt-0+-sound = sound AExpPr 1 0+-func (λ _ -> refl)

-- Example 3

fancy-func : (_ _ _ _ : AExp) -> AExp × AExp
fancy-func = λ a1 a2 b1 b2 ->
  APlus (APlus (APlus (AMult a1 b1) (AMult a1 b2)) (AMult a2 b1)) (AMult a2 b2) ==
    AMult (APlus a1 a2) (APlus b1 b2)

opt-fancy : AExp → AExp
opt-fancy = replace AExpPr 4 fancy-func

test-opt-fancy :
  let    a1 = ANum 0
  in let a2 = AMinus a1 a1
  in let b1 = ANum 1
  in let b2 = AMinus b1 b1
  in opt-fancy
         (AMinus (APlus (APlus (APlus (AMult a1 b1) (AMult a1 b2)) (AMult a2 b1)) (AMult a2 b2)) (ANum 0)) ≡
       (AMinus (AMult (APlus a1 a2) (APlus b1 b2)) (ANum 0))
test-opt-fancy = refl

fancy-lem : ∀ a1 a2 b1 b2 -> a1 * b1 + a1 * b2 + a2 * b1 + a2 * b2 ≡ (a1 + a2) * (b1 + b2)
fancy-lem = solve
  4
  (λ a1 a2 b1 b2 → a1 :* b1 :+ a1 :* b2 :+ a2 :* b1 :+ a2 :* b2 := (a1 :+ a2) :* (b1 :+ b2))
  refl
    where
      open import Data.Nat.Solver
      open +-*-Solver

opt-fancy-sound : ∀ e → aeval (opt-fancy e) ≡ aeval e
opt-fancy-sound = sound AExpPr 4 fancy-func
  (λ a1 a2 b1 b2 -> fancy-lem (aeval a1) (aeval a2) (aeval b1) (aeval b2))

-- This whole approach isn't sound unless it's proven that `replace' pr n f (fst (f e1 e2 ... en))`
-- is equal to `snd (f e1 e2 ... en)` or something of this sort, which is quite hard in general, I
-- assume. But somehow it's not hard for some specific cases, see the ridiculous proofs below.

postulate
  -- I'm just too lazy to prove it.
  isEqualSelf : ∀ e -> (e ≟AExp e) ≡ yes' refl

replace'-ex1-func-behaves-expectedly :
  ∀ e1 e2 -> replace' AExpPr 2 ex1-func (proj₁ (ex1-func e1 e2)) ≡ proj₂ (ex1-func e1 e2)
replace'-ex1-func-behaves-expectedly e1 e2 with e1 ≟AExp e1 | isEqualSelf e1
... | yes' refl | refl with e2 ≟AExp e2 | isEqualSelf e2
... | yes' refl | refl with e1 ≟AExp e1 | isEqualSelf e1
... | yes' refl | refl with e2 ≟AExp e2 | isEqualSelf e2
... | yes' refl | refl with e1 ≟AExp e1 | isEqualSelf e1
... | yes' refl | refl with e2 ≟AExp e2 | isEqualSelf e2
... | yes' refl | refl = refl

replace'-0+-func-behaves-expectedly :
  ∀ e -> replace' AExpPr 1 0+-func (proj₁ (0+-func e)) ≡ proj₂ (0+-func e)
replace'-0+-func-behaves-expectedly e with e ≟AExp e | isEqualSelf e
... | yes' refl | refl = refl

-- Or using a REWRITE rule:

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE isEqualSelf #-}

replace'-ex1-func-behaves-expectedly-using-rewrite :
  ∀ a1 a2 -> replace' AExpPr 2 ex1-func (proj₁ (ex1-func a1 a2)) ≡ proj₂ (ex1-func a1 a2)
replace'-ex1-func-behaves-expectedly-using-rewrite _ _ = refl

replace'-0+-func-behaves-expectedly-using-rewrite :
  ∀ a2 -> replace' AExpPr 1 0+-func (proj₁ (0+-func a2)) ≡ proj₂ (0+-func a2)
replace'-0+-func-behaves-expectedly-using-rewrite _ = refl

replace'-fancy-func-behaves-expectedly-using-rewrite :
  ∀ a1 a2 b1 b2 ->
    replace' AExpPr 4 fancy-func (proj₁ (fancy-func a1 a2 b1 b2)) ≡ proj₂ (fancy-func a1 a2 b1 b2)
replace'-fancy-func-behaves-expectedly-using-rewrite _ _ _ _ = refl
