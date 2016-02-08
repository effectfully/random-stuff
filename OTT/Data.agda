{-# OPTIONS --no-positivity-check --no-termination-check #-}

open import Level renaming (zero to lzero; suc to lsuc; _⊔_ to _⊔ₗ_)
open import Function
open import Relation.Binary.PropositionalEquality renaming (refl to prefl; cong to pcong) using (_≡_)
open import Data.Empty
open import Data.Unit.Base
open import Data.Nat.Base hiding (_+_)
open import Data.Sum
open import Data.Product hiding (zip)
open import Data.List.Base renaming (map to lmap)

infixr 5 _∷₁_
infix  3 _:>_

data List₁ {α β} {A : Set α} (B : A -> Set β) : List A -> Set β where
  []₁  : List₁ B []
  _∷₁_ : ∀ {x xs} -> B x -> List₁ B xs -> List₁ B (x ∷ xs)

map₁ : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : A -> Set γ} {xs}
     -> (∀ {x} -> B x -> C x) -> List₁ B xs -> List₁ C xs
map₁ g  []₁      = []₁
map₁ g (y ∷₁ ys) = g y ∷₁ map₁ g ys

Over : ∀ {ι} -> Set ι -> ∀ α -> Set (ι ⊔ₗ lsuc α)
Over I α = List I -> I -> Set α

record Rose {ι α} {I : Set ι} (F : Over I α) j : Set (ι ⊔ₗ α) where
  inductive
  constructor _:>_
  field
    {is}   : List I
    cons   : F is j
    childs : List₁ (Rose F) is
open Rose using (cons; childs)



infixl 6 _⊔₀_
infixr 0 _+_
infixr 1 _&_
infixr 2 _⇒_
infix  5 _≟ₙ_
infix  3 _≃_ _≅_ _≅s_ _≅s₁_

_⊔₀_ : ℕ -> ℕ -> ℕ
α ⊔₀ 0 = 0
α ⊔₀ β = α ⊔ β

suc₀ : ℕ -> ℕ
suc₀ 0 = 1
suc₀ n = n

record Unit : Set where

mutual
  Prop = Univ 0
  Type = Univ ∘ suc

  data Univ : ℕ -> Set where
    bot   : Prop
    top   : Prop
    unit  : ∀ {α} -> Univ α
    univ  : ∀ α -> Type α
    σ     : ∀ {α β} -> (A : Univ α) -> (⟦ A ⟧ -> Univ β) -> Univ (α ⊔  β)
    π     : ∀ {α β} -> (A : Univ α) -> (⟦ A ⟧ -> Univ β) -> Univ (α ⊔₀ β)
    _+_   : ∀ {α β} -> (A : Univ α) -> Univ β -> Univ (α ⊔ β)
    list  : ∀ {α} -> Univ α -> Univ (suc₀ α)
    list₁ : ∀ {α β} {A : Univ α} -> (⟦ A ⟧ -> Univ β) -> List ⟦ A ⟧ -> Univ (suc₀ β)
    rose  : ∀ {ι α} {I : Univ ι} -> UOver I α -> ⟦ I ⟧ -> Univ (suc₀ α)
      -- Data types needn't store their indices, right?

  UOver : ∀ {ι} -> Univ ι -> ℕ -> Set
  UOver I α = List ⟦ I ⟧ -> ⟦ I ⟧ -> Univ α

  ⟦_⟧ : ∀ {α} -> Univ α -> Set
  ⟦ bot        ⟧ = ⊥
  ⟦ top        ⟧ = ⊤
  ⟦ unit       ⟧ = Unit
  ⟦ univ α     ⟧ = Univ α
  ⟦ σ A B      ⟧ = ∃ λ x -> ⟦ B x ⟧
  ⟦ π A B      ⟧ = ∀   x -> ⟦ B x ⟧
  ⟦ A + B      ⟧ = ⟦ A ⟧ ⊎ ⟦ B ⟧
  ⟦ list  A    ⟧ = List ⟦ A ⟧
  ⟦ list₁ B xs ⟧ = List₁ (λ x -> ⟦ B x ⟧) xs
  ⟦ rose  F j  ⟧ = Rose (λ is j -> ⟦ F is j ⟧) j

prop = univ 0
type = univ ∘ suc

_&_ : ∀ {α β} -> Univ α -> Univ β -> Univ (α ⊔  β)
A & B = σ A λ _ -> B

_⇒_ : ∀ {α β} -> Univ α -> Univ β -> Univ (α ⊔₀ β)
A ⇒ B = π A λ _ -> B

_≟ₙ_ : ℕ -> ℕ -> Prop
zero  ≟ₙ zero  = top
suc n ≟ₙ suc m = n ≟ₙ m
_     ≟ₙ _     = bot

mutual
  _≃_ : ∀ {α β} -> Univ α -> Univ β -> Prop
  bot                  ≃ bot                  = top
  top                  ≃ top                  = top
  unit                 ≃ unit                 = top
  univ α₁              ≃ univ α₂              = α₁ ≟ₙ α₂
  σ A₁ B₁              ≃ σ A₂ B₂              = A₁ ≃ A₂ & B₁ ≅ B₂
  π A₁ B₁              ≃ π A₂ B₂              =
    A₂ ≃ A₁ & π _ λ x₁ -> π _ λ x₂ -> x₂ ≅ x₁ ⇒ B₁ x₁ ≃ B₂ x₂
  (A₁ + B₁)            ≃ (A₂ + B₂)            = A₁ ≃ A₂ & B₁ ≃ B₂
  list  A₁             ≃ list  A₂             = A₁ ≃ A₂
  list₁ B₁ xs₁         ≃ list₁ B₂ xs₂         = B₁ ≅ B₂ & xs₁ ≅ xs₂
  rose {I = I₁} F₁ j₁  ≃ rose {I = I₂} F₂ j₂  = I₁ ≃ I₂ & F₁ ≅ F₂ & j₁ ≅ j₂
  _                    ≃ _                    = bot

  _≅_ : ∀ {α β} {A : Univ α} {B : Univ β} -> ⟦ A ⟧ -> ⟦ B ⟧ -> Prop
  _≅_ {A = bot         } {bot         }  _         _        = top
  _≅_ {A = top         } {top         }  _         _        = top
  _≅_ {A = unit        } {unit        }  _         _        = top
  _≅_ {A = univ α₁     } {univ α₂     }  A₁        A₂       = A₁ ≃ A₂
  _≅_ {A = σ A₁ B₁     } {σ A₂ B₂     } (x₁ , y₁) (x₂ , y₂) = x₁ ≅ x₂ & y₁ ≅ y₂
  _≅_ {A = π A₁ B₁     } {π A₂ B₂     }  f₁        f₂       =
    π _ λ x₁ -> π _ λ x₂ -> x₁ ≅ x₂ ⇒ f₁ x₁ ≅ f₂ x₂
  _≅_ {A = A₁ + B₁     } {A₂ + B₂     } (inj₁ x₁) (inj₁ x₂) = x₁ ≅ x₂
  _≅_ {A = A₁ + B₁     } {A₂ + B₂     } (inj₂ y₁) (inj₂ y₂) = y₁ ≅ y₂
  _≅_ {A = list  A₁    } {list  A₂    }  xs₁       xs₂      = xs₁ ≅s xs₂
  _≅_ {A = list₁ B₁ xs₁} {list₁ B₂ xs₂}  ys₁       ys₂      = ys₁ ≅s₁ ys₂
  _≅_ {A = rose  F₁ j₁ } {rose  F₂ j₂ }  r₁        r₂       =
    let cons₁ :> childs₁ = r₁ ; cons₂ :> childs₂ = r₂ in cons₁ ≅ cons₂ & childs₁ ≅ childs₂
  _≅_                                    _         _        = bot

  _≅s_ : ∀ {α β} {A : Univ α} {B : Univ β} -> ⟦ list A ⟧ -> ⟦ list B ⟧ -> Prop
  []       ≅s []       = top
  x₁ ∷ xs₁ ≅s x₂ ∷ xs₂ = x₁ ≅ x₂ & xs₁ ≅s xs₂
  _        ≅s _        = bot

  _≅s₁_ : ∀ {α β γ δ} {A : Univ α} {B : Univ β}
            {C : ⟦ A ⟧ -> Univ γ} {D : ⟦ B ⟧ -> Univ δ} {xs ys}
        -> ⟦ list₁ C xs ⟧ -> ⟦ list₁ D ys ⟧ -> Prop
  []₁       ≅s₁ []₁       = top
  y₁ ∷₁ ys₁ ≅s₁ y₂ ∷₁ ys₂ = y₁ ≅ y₂ & ys₁ ≅s₁ ys₂
  _         ≅s₁ _         = bot

Coerceᵏ : ∀ {α β} -> (k : ℕ -> ℕ) -> ⟦ α ≟ₙ β ⟧ -> Univ (k α) -> Univ (k β)
Coerceᵏ {0}     {0}     k r  A = A
Coerceᵏ {suc α} {suc β} k r  A = Coerceᵏ (k ∘ suc) r A
Coerceᵏ {0}     {suc _} k ()
Coerceᵏ {suc _} {0}     k ()

Coerce : ∀ {α β} -> ⟦ α ≟ₙ β ⟧ -> Univ α -> Univ β
Coerce = Coerceᵏ id

mutual
  coerce : ∀ {α β} {A : Univ α} {B : Univ β} -> ⟦ A ≃ B ⟧ -> ⟦ A ⟧ -> ⟦ B ⟧
  coerce {A = bot         } {bot         } q ()
  coerce {A = top         } {top         } q tt       = tt
  coerce {A = unit        } {unit        } q _        = _
  coerce {A = univ α₁     } {univ α₂     } q A        = Coerce q A
  coerce {A = σ A₁ B₁     } {σ A₂ B₂     } q p        = let q₁ , q₂ = q ; x , y = p in
    coerce q₁ x , coerce (q₂ x (coerce q₁ x) (coherence q₁ x)) y
  coerce {A = π A₁ B₁     } {π A₂ B₂     } q f        = let q₁ , q₂ = q in λ x ->
    coerce (q₂ (coerce q₁ x) x (coherence q₁ x)) (f (coerce q₁ x))
  coerce {A = A₁ + B₁     } {A₂ + B₂     } q (inj₁ x) = inj₁ (coerce (proj₁ q) x)
  coerce {A = A₁ + B₁     } {A₂ + B₂     } q (inj₂ y) = inj₂ (coerce (proj₂ q) y)
  coerce {A = list  A₁    } {list  A₂    } q  xs      = lmap (coerce q) xs
  coerce {A = list₁ B₁ xs₁} {list₁ B₂ xs₂} q  ys      = let q₁ , q₂ = q in coerces₁ q₁ q₂ ys
  coerce {A = rose  F₁ j₁ } {rose  F₂ j₂ } q  r       =
    let q₁ , q₂ , q₃ = q ; _:>_ {is} cons childs = r ; cs = coherences q₁ is in
         coerce (q₂ is (coerce q₁ is) cs _ _ q₃) cons
      :> coerces₁ (λ x₁ x₂ r₂ -> q₁ , q₂ , r₂) cs childs
  coerce _ _ = zillions-of-impossible-clauses where postulate zillions-of-impossible-clauses : _

  coerces₁ : ∀ {α β γ δ} {A : Univ α} {B : Univ β}
               {C : ⟦ A ⟧ -> Univ γ} {D : ⟦ B ⟧ -> Univ δ} {xs ys}
           -> ⟦ C ≅ D ⇒ xs ≅ ys ⇒ list₁ C xs ⇒ list₁ D ys ⟧
  coerces₁ {ys = []   } q r   []₁      = []₁
  coerces₁ {ys = _ ∷ _} q r  (z ∷₁ zs) = let r₁ , r₂ = r in
    coerce (q _ _ r₁) z ∷₁ coerces₁ q r₂ zs
  coerces₁ {ys = _ ∷ _} q ()  []₁
  coerces₁ {ys = []   } q () (z ∷₁ zs)

  coherences : ∀ {α β} {A : Univ α} {B : Univ β}
             -> (q : ⟦ A ≃ B ⟧) -> (xs : ⟦ list A ⟧) -> ⟦ xs ≅s lmap (coerce q) xs ⟧
  coherences q  []      = tt
  coherences q (x ∷ xs) = coherence q x , coherences q xs

  postulate
    coherence : ∀ {α β} {A : Univ α} {B : Univ β}
              -> (q : ⟦ A ≃ B ⟧) -> (x : ⟦ A ⟧) -> ⟦ x ≅ coerce q x ⟧

postulate
  refl : ∀ {α} {A : Univ α} -> (x : ⟦ A ⟧) -> ⟦ x ≅ x ⟧
  sym  : ∀ {α β} {A : Univ α} {B : Univ β}
       -> ⟦ A ≃ B ⟧ -> (x : ⟦ A ⟧) -> (y : ⟦ B ⟧) -> ⟦ x ≅ y ⇒ y ≅ x ⟧
  huip : ∀ {α β} {A : Univ α} {B : Univ β}
       -> (x : ⟦ A ⟧) -> (y : ⟦ B ⟧) -> (q : ⟦ x ≅ y ⟧) -> ⟦ refl x ≅ q ⟧

subst : ∀ {α π} {A : Univ α} {x y} -> (P : ⟦ A ⟧ -> Univ π) -> ⟦ x ≅ y ⇒ P x ⇒ P y ⟧
subst P q = coerce (refl P _ _ q)

subst₂ : ∀ {α β π} {A : Univ α} {B : ⟦ A ⟧ -> Univ β} {i j} {x : ⟦ B i ⟧} {y : ⟦ B j ⟧}
       -> (P : ∀ x -> ⟦ B x ⟧ -> Univ π) -> ⟦ i ≅ j ⇒ x ≅ y ⇒ P i x ⇒ P j y ⟧
subst₂ P q₁ q₂ = coerce (refl P _ _ q₁ _ _ q₂)



nat : Type 0
nat = rose (λ is _ -> is ≅ (List ⊤ ∋ []) + is ≅ tt ∷ []) tt

Nat : Set
Nat = ⟦ nat ⟧

nzero : Nat
nzero = inj₁ _ :> []₁

nsuc : Nat -> Nat
nsuc n = inj₂ _ :> n ∷₁ []₁

elimNat : ∀ {π} -> (P : Nat -> Set π) -> (∀ {n} -> P n -> P (nsuc n)) -> P nzero -> ∀ n -> P n
elimNat P f x (inj₁  _       :> []₁        ) = x
elimNat P f x (inj₂  _       :> n ∷₁ []₁   ) = f (elimNat P f x n)
elimNat P f x (inj₁  ()      :> _ ∷₁ _     )
elimNat P f x (inj₂  ()      :> []₁        )
elimNat P f x (inj₂ (_ , ()) :> _ ∷₁ _ ∷₁ _)

caseNat : ∀ {π} -> (P : Nat -> Set π) -> (∀ n -> P (nsuc n)) -> P nzero -> ∀ n -> P n
caseNat P f = elimNat P (const (f _))

≅→≡-Nat : (n m : Nat) -> ⟦ n ≅ m ⟧ -> n ≡ m
≅→≡-Nat = elimNat _ (λ r -> caseNat _ (λ m -> pcong nsuc ∘ r m ∘ proj₁ ∘ proj₂) (uncurry λ()))
                    (caseNat _ (λ _ -> uncurry λ()) (λ _ -> prefl))

substNat : ∀ {π} -> (P : Nat -> Set π) -> (n m : Nat) -> ⟦ n ≅ m ⟧ -> P n -> P m
substNat P n m q rewrite ≅→≡-Nat n m q = id

toNat : ℕ -> Nat
toNat = fold nzero nsuc

fromNat : Nat -> ℕ
fromNat = elimNat _ suc 0



infixr 5 _∷ᵥ_

-- A definition via explicit unification constraints.
-- vec : ∀ {α} -> Univ α -> Nat -> Univ (suc₀ (suc zero ⊔ α))
-- vec A = rose (λ is n -> is ≅ (List ⟦ nat ⟧ ∋ []) & n ≅ nzero
--                       + σ nat λ m -> is ≅ m ∷ [] & n ≅ nsuc m & A)

-- (& unit) due to the lack of cumulativity.
vec : ∀ {α} -> Univ α -> Nat -> Univ (suc₀ α)
vec A = rose (λ is -> caseNat _ (λ n -> is ≅ n ∷ [] & A) (is ≅ (List Nat ∋ []) & unit))

Vec : ∀ {α} -> Univ α -> Nat -> Set
Vec A n = ⟦ vec A n ⟧

[]ᵥ : ∀ {α} {A : Univ α} -> Vec A nzero
[]ᵥ = _ :> []₁

_∷ᵥ_ : ∀ {α} {A : Univ α} {n} -> ⟦ A ⟧ -> Vec A n -> Vec A (nsuc n)
_∷ᵥ_ {n = n} x xs = (refl n , tt) , x :> xs ∷₁ []₁

elimVec : ∀ {α π} {A : Univ α} {n}
        -> (P : ∀ {n} -> Vec A n -> Univ π)
        -> (∀ {n} {xs : Vec A n} x -> ⟦ P xs ⇒ P (x ∷ᵥ xs) ⟧)
        -> ⟦ P []ᵥ ⟧
        -> (xs : Vec A n)
        -> ⟦ P xs ⟧
elimVec {A = A} {n} P f z = elimNat (λ n -> ∀ xs -> ⟦ P {n} xs ⟧) elim-∷ᵥ elim-[]ᵥ n where
  elim-[]ᵥ : (xs : Vec A nzero) -> ⟦ P xs ⟧
  elim-[]ᵥ (_  , _ :> []₁   ) = z
  elim-[]ᵥ (() , _ :> _ ∷₁ _)

  -- elim-∷ᵥ : ∀ {n} -> ((xs : Vec A n) -> ⟦ P xs ⟧) -> (xs : Vec A (nsuc n)) -> ⟦ P xs ⟧
  -- elim-∷ᵥ {n} r (_:>_ {n' ∷ []} ((q , tt) , x) (xs ∷₁ []₁)) =
  --   subst₂ {i = n'} (λ m (p : ⟦ n' ≅ m ⟧) -> P ((p , tt) , x :> xs ∷₁ []₁))
  --     q (huip n' n q) (f x (subst (λ m -> π (vec A m) λ xs -> P xs) (sym (refl nat) n' n q) r xs))
  -- elim-∷ᵥ     r (() , _       :> []₁        )
  -- elim-∷ᵥ     r ((_ , ()) , _ :> _ ∷₁ _ ∷₁ _)

  elim-∷ᵥ : ∀ {n} -> ((xs : Vec A n) -> ⟦ P xs ⟧) -> (xs : Vec A (nsuc n)) -> ⟦ P xs ⟧
  elim-∷ᵥ {n} r (_:>_ {n' ∷ []} ((q , tt) , x) (xs ∷₁ []₁)) rewrite ≅→≡-Nat n' n q =
    subst {y = q} (λ q' -> P ((q' , tt) , x :> xs ∷₁ []₁)) (huip n n q) (f x (r xs))
  elim-∷ᵥ     r (() , _       :> []₁        )
  elim-∷ᵥ     r ((_ , ()) , _ :> _ ∷₁ _ ∷₁ _)



plus : Nat -> Nat -> Nat
plus n m = elimNat _ nsuc m n

lengthᵥ : ∀ {n α} {A : Univ α} -> Vec A n -> Nat
lengthᵥ {n} _ = n

sumᵥ : ∀ {n} -> Vec nat n -> Nat
sumᵥ = elimVec _ plus nzero

vec1234 = toNat 1 ∷ᵥ toNat 2 ∷ᵥ toNat 3 ∷ᵥ toNat 4 ∷ᵥ []ᵥ

test₁ : fromNat (lengthᵥ vec1234) ≡ 4
test₁ = prefl

test₂ : fromNat (sumᵥ vec1234) ≡ 10
test₂ = prefl

favourite : (Nat -> Nat) -> Type 0
favourite = rose (λ is f -> σ nat λ n -> f  ≅ ((Nat -> Nat) ∋ const n)
                                       & is ≅ (List (Nat -> Nat) ∋ []))

Favourite : (Nat -> Nat) -> Set
Favourite f = ⟦ favourite f ⟧

fave : ∀ n -> Favourite (const n)
fave n = (n , (λ _ _ _ -> refl n) , tt) :> []₁

deep : Nat -> Nat
deep = elimNat _ id (toNat 4)

const≅deep : ⟦ ((Nat -> Nat) ∋ const (toNat 4)) ≅ deep ⟧
const≅deep n m q = elimNat (λ m -> ⟦ toNat 4 ≅ deep m ⟧) id _ m

test₃ : Favourite deep
test₃ = subst favourite const≅deep (fave (toNat 4))
