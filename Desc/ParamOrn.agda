-- In normal descriptions `π A D` encodes the whole Agda's function space,
-- which allows to define data types that can't be unquoted to actual Agda data types.
-- With the descriptions below it's not possible to define such data types,
-- because `D` in `π A D` receives not an `A`, but a `∀ p -> A p` and that `p`
-- of universally quantified type `P` is provided only to a `var` and
-- to the first argument of a `π`.
-- The untraditional `skip` constructor of `Orn` allows to "cut"
-- higher-order inductive occurrences. E.g. if you have

-- data D : Set where
--   C : (ℕ -> List ℕ -> D) -> D

-- then you can ornament it into

-- data D′ : Set where
--   C′ : (ℕ -> D′) -> D′

-- or even

-- data D′′ : Set where
--   C′′ : D′′ -> D′′

-- The forgetful maps then are `f′ : D′ -> D` and `f′′ : D′′ -> D` with the obvious definitions.

{-# OPTIONS --type-in-type #-}

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit.Base
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Fin hiding (_+_)
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.Vec hiding (_⊛_; _∈_; here; there)

infixr 0 _∸>_
infix  3 _∈_

_∸>_ : ∀ {ι α β} {I : Set ι} -> (I -> Set α) -> (I -> Set β) -> Set _
A ∸> B = ∀ {i} -> A i -> B i

Any : ∀ {n α β} {A : Set α} -> (A -> Set β) -> Vec A n -> Set β
Any B  []      = ⊥
Any B (x ∷ []) = B x
Any B (x ∷ xs) = B x ⊎ Any B xs

_∈_ : ∀ {n α} {A : Set α} -> A -> Vec A n -> Set
x ∈ xs = Any (x ≡_) xs

here : ∀ {n α β} {A : Set α} {B : A -> Set β} {x} -> (xs : Vec A n) -> B x -> Any B (x ∷ xs)
here  []      y = y
here (x ∷ xs) y = inj₁ y

phere : ∀ {n α} {A : Set α} {x : A} -> (xs : Vec A n) -> x ∈ x ∷ xs
phere xs = here xs refl

there : ∀ {n α β} {A : Set α} {B : A -> Set β} {x} -> (xs : Vec A n) -> Any B xs -> Any B (x ∷ xs)
there  []      ()
there (x ∷ xs) a  = inj₂ a

mapAny : ∀ {n α β γ} {A : Set α} {B : A -> Set β} {C : A -> Set γ}
       -> (xs : Vec A n) -> (∀ {x} -> B x -> C x) -> Any B xs -> Any C xs
mapAny  []           g  ()
mapAny (x ∷ [])      g  y       = g y
mapAny (x ∷ x′ ∷ xs) g (inj₁ y) = inj₁ (g y)
mapAny (x ∷ x′ ∷ xs) g (inj₂ r) = inj₂ (mapAny (x′ ∷ xs) g r)

All : ∀ {n α β} {A : Set α} -> (A -> Set β) -> Vec A n -> Set β
All B  []      = ⊤
All B (x ∷ xs) = B x × All B xs

unmap : ∀ {n α β γ} {A : Set α} {B : A -> Set β} {C : Set γ} {xs : Vec A n}
      -> (∀ {x} -> B x -> C) -> All B xs -> Vec C n
unmap {xs = []}     g  tt      = []
unmap {xs = x ∷ xs} g (y , ys) = g y ∷ unmap g ys

mapUnmap : ∀ {n α β γ δ} {A : Set α} {B : A -> Set β} {C : Set γ}
             {D : C -> Set δ} {g : ∀ {x} -> B x -> C} {xs : Vec A n}
         -> (∀ {x} -> x ∈ xs -> (y : B x) -> D (g y)) -> (ys : All B xs) -> All D (unmap g ys)
mapUnmap {g = g} {[]}     h  tt      = tt
mapUnmap {g = g} {x ∷ xs} h (y , ys) = h (phere xs) y , mapUnmap (h ∘ there xs) ys

lookupAnyAll : ∀ {n α β γ} {A : Set α} {B : A -> Set β} {C : A -> Set γ} {xs : Vec A n}
             -> Any B xs -> All C xs -> ∃ λ x -> B x × C x
lookupAnyAll {xs = []}           ()       tt
lookupAnyAll {xs = x ∷ []}       y       (z , tt) = x , y , z
lookupAnyAll {xs = x ∷ x′ ∷ xs} (inj₁ y) (z , zs) = x , y , z
lookupAnyAll {xs = x ∷ x′ ∷ xs} (inj₂ a) (z , zs) = lookupAnyAll a zs

data _⁻¹_ {A B : Set} (f : A -> B) : B -> Set where
  inv : ∀ {y} x -> f x ≡ y -> f ⁻¹ y

arg : ∀ {A B y} {f : A -> B} -> f ⁻¹ y -> A
arg (inv x _) = x

module ParamDesc (P : Set) where
  infixr 6 _⊛_

  data Desc (I : Set) : Set where
    var : (P -> I) -> Desc I
    π   : (A : P -> Set) -> ((∀ p -> A p) -> Desc I) -> Desc I
    _⊛_ : Desc I -> Desc I -> Desc I

open ParamDesc ⊤ using (Desc) public
open ParamDesc renaming (Desc to DescOver) public

AgdaDesc : Set -> Set
AgdaDesc I = ∀ {P} -> ParamDesc.Desc P I

⟦_⟧ : ∀ {I} -> Desc I -> (I -> Set) -> Set
⟦ var i ⟧ B = B (i tt)
⟦ π A D ⟧ B = ∀ x -> ⟦ D (const x) ⟧ B
⟦ D ⊛ E ⟧ B = ⟦ D ⟧ B × ⟦ E ⟧ B

Extend : ∀ {I} -> Desc I -> (I -> Set) -> I -> Set
Extend (var i) B j = i tt ≡ j
Extend (π A D) B j = ∃ λ x -> Extend (D (const x)) B j
Extend (D ⊛ E) B j = ⟦ D ⟧ B × Extend E B j

Data : Set -> ℕ -> Set
Data I = Vec (AgdaDesc I)

data μ {n I} (Ds : Data I n) j : Set where
  node : Any (λ D -> Extend (D {⊤}) (μ Ds) j) Ds -> μ Ds j

module ParamOrn (P : Set) where
  infixr 6 _⊛_

  data Orn {I J : Set} (c : J -> I) : Bool -> DescOver P I -> Set where
    var  : ∀ {i b} -> (∀ p -> c ⁻¹ i p) -> Orn c b (var i)
    keep : ∀ {A D b} -> (∀ x -> Orn c b (D x)) -> Orn c b (π A D)
    _⊛_  : ∀ {D E b} -> Orn c false D -> Orn c b E -> Orn c b (D ⊛ E)
    abst : ∀ {D} -> (A : P -> Set) -> ((∀ p -> A p) -> Orn c true D) -> Orn c true D
    inst : ∀ {A : P -> Set} {D} x -> Orn c true (D x) -> Orn c true (π A D)
    skip : ∀ {A : P -> Set} {D} -> Orn c false D -> Orn c false (π A λ _ -> D)

open ParamOrn ⊤ using (Orn) public
open ParamOrn renaming (Orn to OrnOver) public

AgdaOrn : {I J : Set} -> (J -> I) -> AgdaDesc I -> Set
AgdaOrn c D = ∀ {P} -> ParamOrn.Orn P c true D

DataOrn : ∀ {n} {I J : Set} -> (J -> I) -> Data I n -> Set
DataOrn c = All (AgdaOrn c)

⟦_⟧ᵒ : ∀ {P I J b D} {c : J -> I} -> OrnOver P c b D -> DescOver P J
⟦ var a    ⟧ᵒ = var (arg ∘ a)
⟦ keep O   ⟧ᵒ = π _ λ x -> ⟦ O x ⟧ᵒ
⟦ O ⊛ P    ⟧ᵒ = ⟦ O ⟧ᵒ ⊛ ⟦ P ⟧ᵒ
⟦ abst A O ⟧ᵒ = π _ λ x -> ⟦ O x ⟧ᵒ
⟦ inst x O ⟧ᵒ = ⟦ O ⟧ᵒ
⟦ skip O   ⟧ᵒ = ⟦ O ⟧ᵒ

⟦_⟧ᵈᵒ : ∀ {n} {I J : Set} {c : J -> I} {Ds : Data I n} -> DataOrn c Ds -> Data J n
⟦_⟧ᵈᵒ = unmap (λ O {P} -> ⟦ O {P} ⟧ᵒ)

mapHyp : ∀ {I B C} -> (D : Desc I) -> B ∸> C -> ⟦ D ⟧ B -> ⟦ D ⟧ C
mapHyp (var i) g  y      = g y
mapHyp (π A D) g  f      = λ x -> mapHyp (D (const x)) g (f x)
mapHyp (D ⊛ E) g (x , y) = mapHyp D g x , mapHyp E g y

mapExtend : ∀ {I B C} -> (D : Desc I) -> B ∸> C -> Extend D B ∸> Extend D C
mapExtend (var i) g  q      = q
mapExtend (π A D) g (x , e) = x , mapExtend (D (const x)) g e
mapExtend (D ⊛ E) g (x , e) = mapHyp D g x , mapExtend E g e

Alg : ∀ {I} -> (I -> Set) -> Desc I -> Set
Alg B D = Extend D B ∸> B

{-# TERMINATING #-}
gfold : ∀ {n I B} {Ds : Data I n} -> All (λ D -> Alg B (D {⊤})) Ds -> μ Ds ∸> B
gfold as (node a) = case lookupAnyAll a as of λ
  { (D , e , f) -> f (mapExtend D (gfold as) e)
  }

forgetHyp : ∀ {I J D B} {c : J -> I}
          -> (O : Orn c false D) -> ⟦ ⟦ O ⟧ᵒ ⟧ (B ∘ c) -> ⟦ D ⟧ B
forgetHyp {B = B} (var  a)  y      with a tt
... | inv j r = subst B r y
forgetHyp         (keep O)  f      = λ x -> forgetHyp (O (const x)) (f x)
forgetHyp         (O ⊛ E ) (x , y) = forgetHyp O x , forgetHyp E y
forgetHyp         (skip O)  x      = λ _ -> forgetHyp O x

forgetExtend : ∀ {I J D B} {c : J -> I}
             -> (O : Orn c true D) -> Extend ⟦ O ⟧ᵒ (B ∘ c) ∸> Extend D B ∘ c
forgetExtend (var a   )  q      with a tt | q
... | inv _ r  | refl = sym r
forgetExtend (keep O  ) (x , e) = x , forgetExtend (O (const x)) e
forgetExtend (O ⊛ P   ) (x , e) = forgetHyp O x , forgetExtend P e
forgetExtend (abst A O) (x , e) = forgetExtend (O (const x)) e
forgetExtend (inst x O)  e      = x tt , forgetExtend O e

forgetAlg : ∀ {n I J D} {c : J -> I} {Ds : Data I n}
          -> D ∈ Ds -> (O : Orn c true D) -> Alg (μ Ds ∘ c) ⟦ O ⟧ᵒ
forgetAlg {Ds = Ds} p O e = node $
  mapAny Ds (λ q -> subst (λ D -> Extend (D {⊤}) _ _) q (forgetExtend O e)) p

forget : ∀ {n I J j} {c : J -> I} {Ds : Data I n}
       -> (Os : DataOrn c Ds) -> μ ⟦ Os ⟧ᵈᵒ j -> μ Ds (c j)
forget Os = gfold $ mapUnmap (λ p O {_} e -> forgetAlg p (O {⊤}) e) Os

ovar : ∀ {P I J b} {c : J -> I} -> (i : P -> J) -> OrnOver P c b (var (c ∘ i))
ovar i = var λ p -> inv (i p) refl

Cons : ∀ {I} -> (I -> Set) -> Desc I -> Set
Cons B (var i) = B (i tt)
Cons B (π A D) = ∀ x -> Cons B (D (const x))
Cons B (D ⊛ E) = ⟦ D ⟧ B -> Cons B E

Cons# : ∀ {m I} n -> (I -> Set) -> Data I (suc n + m) -> Set
Cons# n B Ds = Cons B (lookup (inject+ _ (fromℕ n)) Ds)



infixr 5 _∷′_ _∷ᵥ′_

list : Set -> Data ⊤ 2
list A = var (const tt)
       ∷ (π (const A) λ _ -> var (const tt) ⊛ var (const tt))
       ∷ []

List′ : Set -> Set
List′ A = μ (list A) tt

pattern []′       = node (inj₁ refl)
pattern _∷′_ x xs = node (inj₂ (x , xs , refl))

list→vec : ∀ A -> DataOrn (λ (_ : ℕ) -> tt) (list A)
list→vec A = ovar (const 0)
           , (abst (const ℕ) λ n -> keep λ x -> ovar n ⊛ ovar (suc ∘ n))
           , tt

vec′ : Set -> Data ℕ 2
vec′ A = ⟦ list→vec A ⟧ᵈᵒ

Vec′ : Set -> ℕ -> Set
Vec′ A = μ (vec′ A)

pattern []ᵥ′           = node (inj₁ refl)
pattern _∷ᵥ′_ {n} x xs = node (inj₂ (n , x , xs , refl))

elimVec′ : ∀ {n A}
         -> (P : ∀ {n} -> Vec′ A n -> Set)
         -> (∀ {n} x {xs : Vec′ A n} -> P xs -> P (x ∷ᵥ′ xs))
         -> P []ᵥ′ 
         -> (xs : Vec′ A n)
         -> P xs
elimVec′ P f z  []ᵥ′      = z
elimVec′ P f z (x ∷ᵥ′ xs) = f x (elimVec′ P f z xs)

test : forget (list→vec ℕ) (4 ∷ᵥ′ 9 ∷ᵥ′ 3 ∷ᵥ′ 8 ∷ᵥ′ []ᵥ′) ≡ 4 ∷′ 9 ∷′ 3 ∷′ 8 ∷′ []′
test = refl

data Vec′′ A : ℕ -> Set where
  []ᵥ   : Cons# 0 (Vec′′ A) (vec′ A)
  consᵥ : Cons# 1 (Vec′′ A) (vec′ A)

elimVec′′ : ∀ {n A}
          -> (P : ∀ {n} -> Vec′′ A n -> Set)
          -> (∀ {n} x {xs : Vec′′ A n} -> P xs -> P (consᵥ n x xs))
          -> P []ᵥ
          -> (xs : Vec′′ A n)
          -> P xs
elimVec′′ P f z  []ᵥ           = z
elimVec′′ P f z (consᵥ n x xs) = f x (elimVec′′ P f z xs)
