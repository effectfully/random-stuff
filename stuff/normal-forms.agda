-- This is related to http://stackoverflow.com/questions/26615082/how-does-one-prove-a-type-of-the-form-a-b-in-agda

open import Function
open import Relation.Binary.PropositionalEquality

data Int : Set where
  Z : Int
  S : Int -> Int
  P : Int -> Int

normalize : Int -> Int
normalize  Z    = Z
normalize (S n) with normalize n
... | P m = m
... | m = S m
normalize (P n) with normalize n
... | S m = m
... | m = P m

data NormalForm : Int -> Set where
  NZ  : NormalForm Z
  NSZ : NormalForm (S Z)
  NPZ : NormalForm (P Z)
  NSS : ∀ {n} -> NormalForm (S n) -> NormalForm (S (S n))
  NPP : ∀ {n} -> NormalForm (P n) -> NormalForm (P (P n))

normalForm : ∀ n -> NormalForm (normalize n)
normalForm  Z    = NZ
normalForm (S n) with normalize n | normalForm n
... | Z    | nf     = NSZ
... | S  _ | nf     = NSS nf
... | P ._ | NPZ    = NZ
... | P ._ | NPP nf = nf
normalForm (P n) with normalize n | normalForm n
... | Z    | nf     = NPZ
... | S ._ | NSZ    = NZ
... | S ._ | NSS nf = nf
... | P  _ | nf     = NPP nf

idempotent' : ∀ {n} -> NormalForm n -> normalize n ≡ n
idempotent'  NZ     = refl
idempotent'  NSZ    = refl
idempotent'  NPZ    = refl
idempotent' (NSS p) rewrite idempotent' p = refl
idempotent' (NPP p) rewrite idempotent' p = refl

idempotent : ∀ n -> normalize (normalize n) ≡ normalize n
idempotent = idempotent' ∘ normalForm