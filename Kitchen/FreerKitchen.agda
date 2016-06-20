open import Level renaming (zero to lzero; suc to lsuc)
open import Function
open import Relation.Nullary.Decidable
open import Data.Empty
open import Data.Unit.Base
open import Data.Bool.Base hiding (_≟_)
open import Data.Nat.Base  hiding (_⊔_)
open import Data.Product
open import Data.List.Base

infixl 1 _>>=_ _>>_

data IFreer {ι α β γ} {I : Set ι} (F : Set β -> I -> I -> Set γ)
            (A : Set α) : I -> I -> Set (ι ⊔ α ⊔ lsuc β ⊔ γ) where
  pure : ∀ {i} -> A -> IFreer F A i i
  free : ∀ {i j k B} -> F B i j -> (B -> IFreer F A j k) -> IFreer F A i k

_>>=_ : ∀ {ι α β γ δ} {I : Set ι} {F : Set γ -> I -> I -> Set δ} {A : Set α} {B : Set β} {i j k}
      -> IFreer F A i j -> (A -> IFreer F B j k) -> IFreer F B i k 
pure x   >>= f = f x
free a g >>= f = free a λ y -> g y >>= f

_>>_ : ∀ {ι α β γ δ} {I : Set ι} {F : Set γ -> I -> I -> Set δ} {A : Set α} {B : Set β} {i j k}
     -> IFreer F A i j -> IFreer F B j k -> IFreer F B i k 
a >> b = a >>= λ _ -> b

liftF : ∀ {ι α γ} {I : Set ι} {F : Set α -> I -> I -> Set γ} {A : Set α} {i j}
      -> F A i j -> IFreer F A i j
liftF x = free x pure



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

data KitchenF : Set -> List ℕ -> List ℕ -> Set where
  bakeF : ∀ {is} -> KitchenF (Sing (fresh is)) is (fresh is ∷ is)
  eatF  : ∀ {is i} -> (p : i ∈? is) -> Sing i -> KitchenF ⊤ is (remove i is p)

Kitchen : ∀ {α} -> Set α -> List ℕ -> List ℕ -> Set _
Kitchen = IFreer KitchenF

bake : ∀ {is} -> Kitchen (Sing (fresh is)) is (fresh is ∷ is)
bake = liftF bakeF

eat : ∀ {is i} {p : i ∈? is} -> Sing i -> Kitchen ⊤ is (remove i is p)
eat {p = p} c = liftF (eatF p c)

ok : Kitchen ⊤ [] [ _ ]
ok = bake >>= λ brownie ->
     bake >>= λ muffin  ->
     bake >>= λ cupcake ->
     eat  muffin  >>
     eat  brownie >>
     pure _
