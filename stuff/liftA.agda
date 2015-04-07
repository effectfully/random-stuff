open import Level
open import Function

infixl 0 _·_
infixl 9 _%

_·_ = _$_
_%  = _∘_

record Functor {α} (F : Set α -> Set α) : Set (suc α) where
  infixl 4 _<$>_

  field
    _<$>_ : ∀ {A B} -> (A -> B) -> F A -> F B
open Functor {{...}}

record Applicative {α} (F : Set α -> Set α) : Set (suc α) where
  infixl 4 _<*>_

  field
    pure  : ∀ {A} -> A -> F A
    _<*>_ : ∀ {A B} -> F (A -> B) -> F A -> F B

  instance
    Applicative<:Functor : Functor F
    Applicative<:Functor = record { _<$>_ = _<*>_ ∘ pure }
open Applicative {{...}}

record Monad {α} (M : Set α -> Set α) : Set (suc α) where
  infixl 1 _>>=_

  field
    return : ∀ {A} -> A -> M A
    _>>=_  : ∀ {A B} -> M A -> (A -> M B) -> M B

  instance
    Monad<:Applicative : Applicative M
    Monad<:Applicative = record { pure = return ; _<*>_ = λ mf mx -> mf >>= λ f -> mx >>= return ∘ f }
open Monad {{...}}

--------------------

record _~>_ {α β} (A : Set α) (B : Set β) : Set (α ⊔ β) where
  constructor rec
  field apply : A -> B

instance
  Id : ∀ {α} {A : Set α} -> A ~> A
  Id = rec id

  Ap : ∀ {α γ} {A B : Set α} {C : Set γ} {F : Set α -> Set α}
     -> {{_ : F B ~> C}} {{_ : Applicative F}} -> F (A -> B) ~> (F A -> C)
  Ap {{rec r}} = rec (r % ∘ _<*>_)

liftA : ∀ {α γ} {A B : Set α} {C : Set γ} {F : Set α -> Set α}
      -> {{_ : F B ~> C}} {{_ : Applicative F}} -> (A -> B) -> F A -> C
liftA {{rec r}} = _~>_.apply (rec (r % ∘ _<$>_))

-------------------

open import Data.Maybe
open import Data.List

instance
  Maybe-Monad : ∀ {α} -> Monad (Maybe {α})
  Maybe-Monad = record { return = just ; _>>=_ = λ x f -> maybe f nothing x }

  List-Monad  : ∀ {α} -> Monad (List  {α})
  List-Monad  = record { return = [_]  ; _>>=_ = flip concatMap }

open import Data.Nat
open import Data.Product

test-1 : List ℕ -> List ℕ
test-1 = liftA ℕ.suc

test-2 : List ℕ -> List ℕ -> List ℕ
test-2 = liftA _+_

test-3 : List ℕ -> List (ℕ -> ℕ)
test-3 = liftA _+_

test-4 : List (ℕ × ℕ)
test-4 = liftA _,_ · (1 ∷ 2 ∷ 3 ∷ []) · (4 ∷ 5 ∷ [])

-- Note that _·_ is just an infixl synonym of _$_
yellow : List (ℕ × ℕ)
yellow = liftA _,_   (1 ∷ 2 ∷ 3 ∷ [])   (4 ∷ 5 ∷ [])
