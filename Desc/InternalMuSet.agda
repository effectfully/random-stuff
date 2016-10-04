open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty
open import Data.Unit.Base
open import Data.Sum
open import Data.Product

infixr 0 _▶_
infixr 5 _⊕_
infixr 6 _⊛_
infixr 8 _⊚_
infixr 9 _⊞_

Over : Set -> Set₁
Over I = I -> Set

_<|>_ : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ} -> (A -> C) -> (B -> C) -> A ⊎ B -> C
_<|>_ = [_,_]

_▷_ : Set -> Set -> Set₁
I ▷ O = Over I -> Over O

data _▶_ (I : Set) : Set -> Set₁ where
  arg : ∀ {O}   -> I -> I ▶ O
  ret : ∀ {O}   -> O -> I ▶ O
  _⊕_ : ∀ {O}   -> I ▶ O -> I ▶ O -> I ▶ O
  _⊛_ : ∀ {O}   -> I ▶ O -> I ▶ O -> I ▶ O
  _⊚_ : ∀ {O U} -> U ▶ O -> I ▶ U -> I ▶ O
  _⊞_ : ∀ {O U} -> I ▶ O -> I ▶ U -> I ▶ O ⊎ U
  κ   : ∀ {O}   -> Set -> I ▶ O
  σ   : ∀ {O}   -> (A : Set) -> (A -> I ▶ O) -> I ▶ O
  mu  : ∀ {O}   -> I ⊎ O ▶ O -> I ▶ O 

mutual
  ⟦_⟧ : ∀ {I O} -> I ▶ O -> I ▷ O
  ⟦ arg i ⟧ B j = B i
  ⟦ ret i ⟧ B j = i ≡ j
  ⟦ D ⊕ E ⟧ B j = ⟦ D ⟧ B j ⊎ ⟦ E ⟧ B j
  ⟦ D ⊛ E ⟧ B j = ⟦ D ⟧ B j × ⟦ E ⟧ B j
  ⟦ E ⊚ D ⟧ B j = ⟦ E ⟧ (⟦ D ⟧ B) j
  ⟦ D ⊞ E ⟧ B j = (⟦ D ⟧ B <|> ⟦ E ⟧ B) j
  ⟦ κ A   ⟧ B j = A
  ⟦ σ A D ⟧ B j = ∃ λ x -> ⟦ D x ⟧ B j
  ⟦ mu F  ⟧ B j = μ F B j

  data μ {I O} (F : I ⊎ O ▶ O) (B : Over I) (j : O) : Set where
    node : ⟦ F ⟧ (B <|> μ F B) j -> μ F B j

top : ∀ {I O} -> I ▶ O
top = κ ⊤

[_]ₚ_ : ∀ {I O U} -> I ▶ O -> I -> U ▶ O
[ D ]ₚ i = D ⊚ ret i

[_]ᵢ_ : ∀ {I O U} -> I ▶ O -> O -> I ▶ U
[ D ]ᵢ i = arg i ⊚ D

⟦_⟧⁽⁾ : ⊥ ▶ ⊤ -> Set
⟦ D ⟧⁽⁾ = ⟦ D ⟧ (λ()) tt



list : ⊤ ▶ ⊤
list = mu
     $ top
     ⊕ arg (inj₁ tt) ⊛ arg (inj₂ tt)

List : Set -> Set
List A = ⟦ list ⟧ (const A) tt

pattern []       = node (inj₁  tt)
pattern _∷_ x xs = node (inj₂ (x , xs))

elimList : ∀ {π A}
         -> (P : List A -> Set π) -> (∀ {xs} x -> P xs -> P (x ∷ xs)) -> P [] -> ∀ xs -> P xs
elimList P f z  []      = z
elimList P f z (x ∷ xs) = f x (elimList P f z xs)

All : ∀ {A} -> (B : A -> Set) -> List A -> Set
All B = elimList _ (λ x Bs -> B x × Bs) ⊤

all : ∀ {A} {B : A -> Set} -> (∀ x -> B x) -> ∀ xs -> All B xs
all f = elimList (All _) (λ x ys -> f x , ys) tt

rose : ⊤ ▶ ⊤
rose = mu
     $ arg (inj₁ tt) ⊛ (list ⊚ arg (inj₂ tt))

Rose : Set -> Set
Rose A = ⟦ rose ⟧ (const A) tt 

-- fork : ∀ {A} -> A -> List (Rose A) -> Rose A 
pattern fork x rs = node (x , rs)

{-# TERMINATING #-}
elimRose : ∀ {A}
         -> (P : Rose A -> Set) -> (∀ {rs} x -> All P rs -> P (fork x rs)) -> ∀ r -> P r
elimRose P f (fork x rs) = f x (all (elimRose P f) rs)

bool : ⊥ ▶ ⊤
bool = top
     ⊕ top

pattern true  = inj₁ tt
pattern false = inj₂ tt

nat : ⊥ ▶ ⊤
nat = mu
    $ top
    ⊕ arg (inj₂ tt)

pattern zero   = node (inj₁ tt)
pattern suc  n = node (inj₂ n)

list₂ : ⊤ ⊎ ⊤ ▶ ⊤
list₂ = mu
      $ top
      ⊕ arg (inj₁ (inj₁ tt)) ⊛ arg (inj₁ (inj₂ tt)) ⊛ arg (inj₂ tt)

List₂ : Set -> Set -> Set
List₂ A B = ⟦ list₂ ⟧ (const A <|> const B) tt

pattern cons₂ x y xs = node (inj₂ (x , y , xs))

example : ⟦ list₂ ⊚ bool ⊞ nat ⟧⁽⁾
example = cons₂ true zero (cons₂ false (suc (suc zero)) [])

-- So the example with AST from the paper doesn't actually require the reindexing operator.
nat′ : ∀ {A} -> ⊤ ⊎ A ▶ A
nat′ = arg tt ⊚ nat ⊚ arg (inj₁ tt)

ilist : ∀ I -> I ▶ ⊤
ilist I = mu
        $ top
        ⊕ σ I λ i -> arg (inj₁ i) ⊛ arg (inj₂ tt)

IList : ∀ {I} -> (I -> Set) -> Set
IList A = ⟦ ilist _ ⟧ A tt

pattern []ᵢ           = node (inj₁  tt)
pattern _∷ᵢ_ {i} x xs = node (inj₂ (i , x , xs))

elimIList : ∀ {π I} {A : I -> Set}
          -> (P : IList A -> Set π)
          -> (∀ {i xs} -> (x : A i) -> P xs -> P (x ∷ᵢ xs))
          -> P []ᵢ
          -> ∀ xs
          -> P xs
elimIList P f z  []ᵢ      = z
elimIList P f z (x ∷ᵢ xs) = f x (elimIList P f z xs)
