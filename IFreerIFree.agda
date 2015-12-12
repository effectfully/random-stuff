open import Level
open import Function
open import Data.Unit.Base
open import Data.Product

infixl 1 _>>=ᵣ_ _>>ᵣ_

data IFreer {ι α β γ} {I : Set ι} (F : Set β -> I -> I -> Set γ)
            (A : Set α) : I -> I -> Set (ι ⊔ α ⊔ suc β ⊔ γ) where
  pureᵣ : ∀ {i} -> A -> IFreer F A i i
  freeᵣ : ∀ {i j k B} -> F B i j -> (B -> IFreer F A j k) -> IFreer F A i k

_>>=ᵣ_ : ∀ {ι α β γ δ} {I : Set ι} {F : Set γ -> I -> I -> Set δ} {A : Set α} {B : Set β} {i j k}
      -> IFreer F A i j -> (A -> IFreer F B j k) -> IFreer F B i k 
pureᵣ x   >>=ᵣ f = f x
freeᵣ a g >>=ᵣ f = freeᵣ a λ y -> g y >>=ᵣ f

_>>ᵣ_ : ∀ {ι α β γ δ} {I : Set ι} {F : Set γ -> I -> I -> Set δ} {A : Set α} {B : Set β} {i j k}
     -> IFreer F A i j -> IFreer F B j k -> IFreer F B i k 
a >>ᵣ b = a >>=ᵣ λ _ -> b

liftFᵣ : ∀ {ι α β γ} {I : Set ι} {F : Set β -> I -> I -> Set γ} {A : Set α} {B : Set β} {i j}
       -> F B i j -> (B -> A) -> IFreer F A i j
liftFᵣ x g = freeᵣ x (pureᵣ ∘ g)



infixr 0 _◃_
infixl 1 _>>=_ _>>_

record IContainer {ι} (I : Set ι) σ π : Set (ι ⊔ suc (σ ⊔ π)) where
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



toIFree : ∀ {ι α β γ} {I : Set ι} {F : Set β -> I -> I -> Set γ} {A : Set α} {i j}
        -> IFreer F A i j -> IFree (∃ ∘ flip (uncurry ∘ F) ◃ λ _ -> proj₁) A i j
toIFree (pureᵣ x)   = pure x
toIFree (freeᵣ a g) = free (, a) (λ y -> toIFree (g y))

toIFreer : ∀ {ι σ π α} {I : Set ι} {C : IContainer (I × I) σ π} {A : Set α} {i j}
         -> IFree C A i j -> IFreer (curry ∘ ⟦ C ⟧ᵢ) A i j
toIFreer (pure x)    = pureᵣ x
toIFreer (free sh r) = freeᵣ (sh , id) (λ p -> toIFreer (r p))
