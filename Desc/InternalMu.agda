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
infixr 9 _⊗_

Over : Set -> Set₁
Over I = I -> Set

_<|>_ : ∀ {A B} -> Over A -> Over B -> Over (A ⊎ B)
(B <|> C) (inj₁ x) = B x
(B <|> C) (inj₂ y) = C y

_▷_ : Set -> Set -> Set₁
I ▷ O = Over I -> Over O

mutual
  data _▶_ (I : Set) : Set -> Set₁ where
    top : ∀ {O}   -> I ▶ O
    arg : ∀ {O}   -> I -> I ▶ O
    ret : ∀ {O}   -> O -> I ▶ O
    _⊕_ : ∀ {O}   -> I ▶ O -> I ▶ O -> I ▶ O
    _⊛_ : ∀ {O}   -> I ▶ O -> I ▶ O -> I ▶ O
    _⊗_ : ∀ {O U} -> I ▶ O -> I ▶ U -> I ▶ O ⊎ U
    _⊚_ : ∀ {O U} -> U ▶ O -> I ▶ U -> I ▶ O
    σ   : ∀ {O}   -> (D : ⊥ ▶ ⊤) -> (⟦ D ⟧⁽⁾ -> I ▶ O) -> I ▶ O
    mu  : ∀ {O}   -> I ⊎ O ▶ O -> I ▶ O 
    wk  : ∀ {O I′ O′} -> (I′ -> I) -> (O -> O′) -> I′ ▶ O′ -> I ▶ O

  ⟦_⟧ : ∀ {I O} -> I ▶ O -> I ▷ O
  ⟦ top      ⟧ B j = ⊤
  ⟦ arg i    ⟧ B j = B i
  ⟦ ret i    ⟧ B j = i ≡ j
  ⟦ D ⊕ E    ⟧ B j = ⟦ D ⟧ B j ⊎ ⟦ E ⟧ B j
  ⟦ D ⊛ E    ⟧ B j = ⟦ D ⟧ B j × ⟦ E ⟧ B j
  ⟦ D ⊗ E    ⟧ B j = [ ⟦ D ⟧ B , ⟦ E ⟧ B ]′ j
  ⟦ σ D E    ⟧ B j = ∃ λ x -> ⟦ E x ⟧ B j
  ⟦ E ⊚ D    ⟧ B j = ⟦ E ⟧ (⟦ D ⟧ B) j
  ⟦ mu F     ⟧ B j = μ F B j 
  ⟦ wk f g D ⟧ B j = ⟦ D ⟧ (B ∘ f) (g j)

  ⟦_⟧⁽⁾ : ⊥ ▶ ⊤ -> Set
  ⟦ D ⟧⁽⁾ = ⟦ D ⟧ (λ()) tt

  data μ {I O} (F : I ⊎ O ▶ O) (B : Over I) (j : O) : Set where
    node : ⟦ F ⟧ (B <|> μ F B) j -> μ F B j

[_]ₚ_ : ∀ {I O} -> I ▶ O -> I -> ⊥ ▶ O
[ D ]ₚ i = D ⊚ ret i

[_]ᵢ_ : ∀ {I O} -> I ▶ O -> O -> I ▶ ⊤
[ D ]ᵢ i = arg i ⊚ D



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

example : ⟦ list₂ ⊚ bool ⊗ nat ⟧⁽⁾
example = cons₂ true zero (cons₂ false (suc (suc zero)) [])

-- So the example with AST from the paper doesn't actually require the reindexing operator.
nat′ : ∀ {A} -> ⊤ ⊎ A ▶ A
nat′ = arg tt ⊚ nat ⊚ arg (inj₁ tt)
