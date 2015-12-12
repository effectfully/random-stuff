open import Level renaming (zero to lzero; suc to lsuc)
open import Function
open import Relation.Nullary.Decidable
open import Data.Empty
open import Data.Unit.Base
open import Data.Bool.Base hiding (_≟_)
open import Data.Nat.Base  hiding (_⊔_)
open import Data.Product
open import Data.List.Base

infixr 0 _◃_
infixl 1 _>>=_ _>>_

record IContainer {ι} (I : Set ι) σ π : Set (ι ⊔ lsuc (σ ⊔ π)) where
  constructor _◃_
  field
    Shape    : I -> Set σ
    Position : ∀ i -> Shape i -> Set π

  ⟦_⟧ᵢ : ∀ {α} -> Set α -> I -> Set (σ ⊔ π ⊔ α)
  ⟦_⟧ᵢ A i = ∃ λ sh -> Position i sh -> A
open IContainer

data IFree {ι σ π α} {I : Set ι} (C : IContainer (I × I) σ π)
           (A : Set α) : I -> I -> Set (ι ⊔ σ ⊔ π ⊔ α) where
  pure : ∀ {i} -> A -> IFree C A i i
  free : ∀ {i j k} sh -> (Position C (i , j) sh -> IFree C A j k) -> IFree C A i k

_>>=_ : ∀ {ι σ π α β} {I : Set ι} {C : IContainer (I × I) σ π} {A : Set α} {B : Set β} {i j k}
      -> IFree C A i j -> (A -> IFree C B j k) -> IFree C B i k 
pure x    >>= f = f x
free sh r >>= f = free sh λ p -> r p >>= f

_>>_ : ∀ {ι σ π α β} {I : Set ι} {C : IContainer (I × I) σ π} {A : Set α} {B : Set β} {i j k}
     -> IFree C A i j -> IFree C B j k -> IFree C B i k 
a >> b = a >>= λ _ -> b

liftF : ∀ {ι σ π α} {I : Set ι} {C : IContainer (I × I) σ π} {A : Set α} {i j}
      -> ⟦ C ⟧ᵢ A (i , j) -> IFree C A i j
liftF (sh , el) = free sh (pure ∘ el)



record Sing {α} {A : Set α} (x : A) : Set where

_==_ : ℕ -> ℕ -> Bool
n == m = ⌊ n ≟ m ⌋

_∈?_ : ℕ -> List ℕ -> Set
n ∈? ns = foldr (λ m r -> if n == m then ⊤ else r) ⊥ ns

remove : ∀ n ns -> n ∈? ns -> List ℕ
remove n  []      ()
remove n (m ∷ ns) p  with n == m
... | true  = ns
... | false = m ∷ remove n ns p

fresh : List ℕ -> ℕ
fresh  []      = 0
fresh (n ∷ ns) = suc n

data Kitchen-Shape (is : List ℕ) : List ℕ -> Set where
  bakeˢ : Kitchen-Shape is (fresh is ∷ is)
  eatˢ  : ∀ {i} -> (p : i ∈? is) -> Sing i -> Kitchen-Shape is (remove i is p)

Kitchen-Position : ∀ {is os} -> Kitchen-Shape is os -> Set
Kitchen-Position {is}  bakeˢ     = Sing (fresh is)
Kitchen-Position      (eatˢ p c) = ⊤

Kitchen-Container : IContainer (List ℕ × List ℕ) lzero lzero
Kitchen-Container = record
  { Shape    = uncurry Kitchen-Shape
  ; Position = λ _ -> Kitchen-Position
  }
  
Kitchen : ∀ {α} -> Set α -> List ℕ -> List ℕ -> Set α
Kitchen = IFree Kitchen-Container

bake : ∀ {is} -> Kitchen (Sing (fresh is)) is (fresh is ∷ is)
bake = liftF (bakeˢ , id)

eat : ∀ {is i} {p : i ∈? is} -> Sing i -> Kitchen ⊤ is (remove i is p)
eat {p = p} c = liftF (eatˢ p c , _)

ok : Kitchen ⊤ [] [ _ ]
ok = bake >>= λ brownie ->
     bake >>= λ muffin  ->
     bake >>= λ cupcake ->
     eat  brownie >>
     eat  muffin  >>
     pure _
