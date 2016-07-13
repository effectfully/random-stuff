open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Sum
open import Data.Product
open import Category.Applicative

IdApplicative : ∀ {α} -> RawApplicative {α} id
IdApplicative = record
  { pure = id
  ; _⊛_  = _$_
  }

SomeApplicative : Set₁
SomeApplicative = ∃ RawApplicative

module _ (someApp : SomeApplicative) where
  infixr 5 _∣_
  infixr 6 _&_

  open Σ someApp renaming (proj₁ to Some; proj₂ to rawApp)
  open RawApplicative rawApp

  data Desc (I : Set) : Set₁ where
    var     : Some I -> Desc I
    π       : (A : Set) -> (Some A -> Desc I) -> Desc I
    _∣_ _&_ : Desc I -> Desc I -> Desc I

  ⟦_⟧ : ∀ {I} -> Desc I -> (Some I -> Set) -> Set
  ⟦ var i ⟧ B = B i
  ⟦ π A D ⟧ B = ∀ x -> ⟦ D x ⟧ B
  ⟦ D ∣ E ⟧ B = ⟦ D ⟧ B ⊎ ⟦ E ⟧ B
  ⟦ D & E ⟧ B = ⟦ D ⟧ B × ⟦ E ⟧ B

  Extend : ∀ {I} -> Desc I -> (Some I -> Set) -> Some I -> Set
  Extend (var i) B j = i ≡ j
  Extend (π A D) B j = ∃ λ x -> Extend (D x) B j
  Extend (D ∣ E) B j = Extend D B j ⊎ Extend E B j
  Extend (D & E) B j = ⟦ D ⟧ B × Extend E B j

  data μ {I} (D : Desc I) j : Set where
    node : Extend D (μ D) j -> μ D j



module _ {someApp : SomeApplicative} where
  open RawApplicative (proj₂ someApp)

  vec : Set -> Desc someApp ℕ
  vec A = var (pure 0)
        ∣ π ℕ λ n -> π A λ _ -> var n & var (suc <$> n)

Vec : Set -> ℕ -> Set
Vec A = μ (_ , IdApplicative) (vec A)

pattern []           = node (inj₁ refl)
pattern _∷_ {n} x xs = node (inj₂ (n , x , xs , refl))

elimVec : ∀ {n A}
        -> (P : ∀ {n} -> Vec A n -> Set)
        -> (∀ {n} x {xs : Vec A n} -> P xs -> P (x ∷ xs))
        -> P []
        -> (xs : Vec A n)
        -> P xs
elimVec P f z  []      = z
elimVec P f z (x ∷ xs) = f x (elimVec P f z xs)
