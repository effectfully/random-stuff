{-
This is related to http://stackoverflow.com/questions/24475546/non-tedious-ast-transformation-proofs-in-agda/

The gist is, given this:

    data AExp : Set where
      ANum : ℕ → AExp
      APlus AMinus AMult : AExp → AExp → AExp

    aeval : AExp → ℕ
    aeval (ANum x) = x
    aeval (APlus a b) = aeval a + aeval b
    aeval (AMinus a b) = aeval a ∸ aeval b
    aeval (AMult a b) = aeval a * aeval b

    transform : (AExp → AExp) → AExp → AExp
    transform f (ANum x)     = f (ANum x)
    transform f (APlus a b)  = f (APlus  (transform f a) (transform f b))
    transform f (AMinus a b) = f (AMinus (transform f a) (transform f b))
    transform f (AMult a b)  = f (AMult  (transform f a) (transform f b))

    opt-0+ : AExp → AExp
    opt-0+ = transform (λ {(APlus (ANum 0) b) → b; x → x})

how does one prove

    opt-0+-sound : ∀ e → aeval (opt-0+ e) ≡ aeval e

with minimal effort?

I'd eventually come up with an approach allowing one to prove such a property in a single line of
code without any generics, here's an example:

    0+-func : AExp -> AExp × AExp
    0+-func = λ a2 -> APlus (ANum 0) a2 == a2

    opt-0+ : AExp → AExp
    opt-0+ = replace AExpPr 1 0+-func

    opt-0+-sound : ∀ e → aeval (opt-0+ e) ≡ aeval e
    opt-0+-sound = sound AExpPr 1 0+-func (λ _ -> refl)

and it scales to more complex cases with functions taking multiple variables etc, see below for full
code.

There are two tricks here.

The main thing that allows us to prove that the bottom-up traversal defined as

    transform : (AExp → AExp) → AExp → AExp
    transform f (ANum x)     = f (ANum x)
    transform f (APlus a b)  = f (APlus  (transform f a) (transform f b))
    transform f (AMinus a b) = f (AMinus (transform f a) (transform f b))
    transform f (AMult a b)  = f (AMult  (transform f a) (transform f b))

preserves the meaning of an expression is this one:

    generalize : ∀ f -> (∀ e -> aeval (f e) ≡ aeval e)
               -> (∀ e -> aeval (transform f e) ≡ aeval e)
    generalize f p (ANum x)     = p (ANum x)
    generalize f p (APlus a b)  rewrite p (APlus  (transform f a) (transform f b))
      | generalize f p a | generalize f p b = refl
    generalize f p (AMinus a b) rewrite p (AMinus (transform f a) (transform f b))
      | generalize f p a | generalize f p b = refl
    generalize f p (AMult a b)  rewrite p (AMult  (transform f a) (transform f b))
      | generalize f p a | generalize f p b = refl

The type signature says that as long as function `f` preserves the meaning of any expression `e`,
`transform f` preserves it as well. It's a fairly natural thing to prove and so as you can see the
proof is straightforward.

Having this simple definition is enough to prove that some trivial optimization preserves the
meaning of an expression, for example

    idAExp : AExp → AExp
    idAExp = transform id

    idAExp-sound : ∀ e → aeval (idAExp e) ≡ aeval e
    idAExp-sound = generalize _ (λ _ → refl)

But things become much more complex when the optimization isn't as trivial, for example even just
defining an optimization turning `a1 * b1 + a1 * b2 + a2 * b1 + a2 * b2` into `(a1 + a2) * (b1 + b2)
is` pretty annoying, because you need not only to have a really deep nested pattern match, but also
check those `a1`, `b1` etc for equality because the pattern is non-linear (i.e. same variables
appear multiple times) and to the best of my knowledge Agda doesn't support non-linear patterns,
hence your only option is to check the equality of terms manually. And then you need to repeat all
of that for the proving part. You can see how that looks like in my answer
(https://stackoverflow.com/a/24479417/3237465) with `fancy-f3` for the defining part and `fancy-p3`
for the proving part.

I'm going to explain it with an example using Haskell instead of Agda.

In order to define `fancy-f3` we need to check whether the input term matches the given pattern and
replace it with some other term if so. Let's instead consider a simpler task of just identifying
whether the input term matches some arbitrary pattern. Let's also drop all the n-arity and say that
we're only interested in 2-argument functions. And let's use lists instead of terms, all for the
sake of clarity.

As in the Agda code we're going to define "patterns" as regular functions. Here's our example
function:

    example :: Integer -> Integer -> [Integer]
    example a b = [4, a, b, 2, a]

How do we check whether a list matches `[4, a, b, 2, a]` for some `a` and `b`? I'm going to
illustrate it with a trick that I occasionally use to constraint type-level values, for example
here's how to say that some type-level list `xs` is non-empty:

type IsCons xs = xs ~ (Head xs ': Tail xs)

This says that `xs` is non-empty as long as it starts with the `(:)` constructor (with a tick
because it's at the type level) and the arguments of that constructor are taken directly from `xs`.

We can use the same strategy to extract `a` and `b` out of the given list to feed them into
`example` to hopeffully get the same list back, which would mean that the list matches the pattern.

I.e. take, say, `[4, 3, 1, 2, 3]`, if we somehow figure out that `a` is at index `1` and `b` is at
index `2`, then we can extract their values (`3` and `1` respectively), feed them into `example` and
get the same `[4, 3, 1, 2, 3]` list back, which indicates that the list matches the pattern.

It only remains to come up with a strategy to extract the indices of `a` and `b`. And that is
actually quite simple: just instantiate `example` twice with arbitrary distinct values and check
where the resulting lists diverge. E.g. `example 1 3` vs `example 5 7` is

    [4, 1, 3, 2, 1] vs
    [4, 5, 7, 2, 5]

and we can clearly see that the two lists diverge at indices `1`, `2` and `4`, meaning those values
must come from the variables. Given that we see that at indices `1` and `4` the lists diverge the
same way, we know that those correspond to the same variable and so we leave only one of them. From
all of that we learn that the value for the one variable can be extracted at index `1` and the value
for the other variable can be extracted at index `2`.

It only remains to actually extract those values from the given list, feed them back into `example`
and check whether the result matches the original list, i.e.

    example ([4, 3, 1, 2, 3] !! 1) ([4, 3, 1, 2, 3] !! 2) == [4, 3, 1, 2, 3]
    example 3 1                                           == [4, 3, 1, 2, 3]
    (\a b -> [4, a, b, 2, a]) 3 1                         == [4, 3, 1, 2, 3]
    [4, 3, 1, 2, 3]                                       == [4, 3, 1, 2, 3]
    True

And this is how we learn that `[4, 3, 1, 2, 3]` matches `[4, a, b, 2, a]`.

Now this isn't the whole story, we also need to sort the index properly to feed them into `example`
in the right order, implement the proving part in case of Agda etc, but it should be enough to
understand the main trick.

The whole fairly short Haskell implementation can be found here:
https://gist.github.com/effectfully/abb9a365f9723038e3303884f6f95118

The function that I called `getSubterms` there returns the values in the original lists at the
indices that are determined to correspond to variables. It's called this way to match `getSubterms`
from the Agda code:
https://github.com/effectfully/random-stuff/blob/1de28312a95446e69fac537eaf88d4f311dc8724/AST_transformation_proofs.agda#L113-L115

Compare how `getSubterms` is used in the Haskell code:

    isMatching :: (Integer -> Integer -> [Integer]) -> [Integer] -> Bool
    isMatching f xs = case getSubterms f xs of
      Nothing     -> False
      Just (x, y) -> f x y == xs

and how it's used in the Agda code:

    replace' : {α β : Level} {A : Set α} {B : Set β}
             -> Proving A B -> (n : ℕ) -> nary n A (A × A) -> A -> A
    replace' pr n f e with getSubterms pr n f e
    replace' pr n f e | nothing = e
    replace' pr n f e | just xs with vecApply n f xs
    replace' pr n f e | just xs |  e' , e'' with Proving._≟A_ pr e e'
    replace' pr n f e | just xs |  e' , e'' | no'       = e
    replace' pr n f e | just xs | .e  , e'' | yes' refl = e''

It's all the same logic: extract the values corresponding to variables, feed them back into the
function and check for equality. Except in Agda we handle the general n-ary case and either replace
the pattern with another expression or return the original one (if it doesn't match the pattern)
rather than merely return `True`/`False`.

Soundness of `replace'` follows the structure very directly:

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

and the rest is the straightforward first trick with `transform` & `generalize`.

One obvious deficiency is that some function may decide to branch on its inputs making it impossible
for us to test whether the lists diverge because we rely on feeding specific inputs to such
functions and who knows what the function may do with them if it decides to branch on them, maybe at
different inputs it returns lists of different lengths etc. I.e. it's the standard issue of HOAS
representing a larger space of acceptable programs that what it's supposed to and may or may not be
addressed the same way (by prepending P to it). This is a deficiency with the Agda code as well, so
we do know that illegitimate usage of the machinery will get you undefined behavior, although you'll
still get a "soundness proof" for that undefined behavior, whatever that even means.

Note that this approach doesn't immediately allow us to prove that some user-defined function
preserves the semantics, we only prove that some blackbox function returned from the complex
machinery preserves the semantics and no relation between the original function and the blackbox one
is established. Meaning that for all we know the blackbox function may not properly correspond to
what was written by the user, until proven otherwise (sure there are a few tests and probably some
more or less sensible informal reasoning, but that's nowhere near being a proof).

I got curious how hard it would be to prove that specific functions behave as expected and
apparently turning a fairly trivial lemma

    isEqualSelf : ∀ e -> (e ≟AExp e) ≡ yes' refl

into a `REWRITE` rule allows us to prove that a function-turned-into-optimization behaves as
expected via just `refl`, i.e. it literally holds definitionally. And we wouldn't even need the
`REWRITE` rule if we had access to a definitional equality checker in Agda (like what was proposed
here: https://lists.chalmers.se/pipermail/agda/2010/001670.html), it'd still be `refl`. We can still
prove that an optimization behaves as expected without any of that, but then it's not `refl` as we
have to discharge a bunch of stupid `e ≟AExp e`.

So it seems like we can actually define an optimization declaratively in Agda and prove that it
behaves as expected and is sound in O(1) lines of code. We can't extract it into Haskell, because
the extra equality checks are going to be very inefficient, but even that is likely addressable if
the imaginary Agda definitional equality checker after extraction becomes some sort of unsafe
pointer equality on the Haskell side, so that comparing a subterm to itself short-circuits
evaluation -- or maybe if we have fancier equality checking function that doesn't attempt to check
equality of things that we know are equal.

Although we only prove that the optimization spots the right pattern and acts on it correctly. We
don't have a proof that in all other cases it doesn't do anything. Not sure how important that is
though, given that we do prove that the meaning of the term is preserved.

In any case I didn't really expect that one could go that far with proof automation without almost
any reflection (only with the fairly trivial isEqualSelf `REWRITE` rule or the like). Pretty sweet!
-}

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
