-- Based on https://github.com/gallais/potpourri/blob/master/agda/poc/PigeonHole.agda

open import Function
open import Data.Nat
open import Data.Sum
open import Data.List hiding (map)

infix 3 _∈_ _⊆_

data _∈_ {α} {A : Set α} (x : A) : List A -> Set where
  here  : ∀ {xs} -> x ∈ x ∷ xs
  there : ∀ {xs y} -> x ∈ xs -> x ∈ y ∷ xs

data repeats {α} {A : Set α} : List A -> Set where
  this  : ∀ {x xs} -> x ∈ xs -> repeats (x ∷ xs)
  other : ∀ {x xs} -> repeats xs -> repeats (x ∷ xs)

_⊆_ : ∀ {α} {A : Set α} -> List A -> List A -> Set α
xs ⊆ ys = ∀ {z} -> z ∈ xs -> z ∈ ys

swap : ∀ {α} {A : Set α} {x y} {xs : List A} -> x ∷ y ∷ xs ⊆ y ∷ x ∷ xs
swap  here             = there here
swap (there  here)     = here
swap (there (there r)) = there (there r)

cut : ∀ {α} {A : Set α} {x} {xs ys : List A} -> x ∷ xs ⊆ x ∷ ys -> x ∈ xs ⊎ xs ⊆ ys
cut {xs = []}     p = inj₂ λ()
cut {xs = x ∷ xs} p with p (there here)
... | here       = inj₁ here
... | there x∈ys = map there aux $ cut (p ∘ swap ∘ there) where
  aux : _ -> x ∷ xs ⊆ _
  aux p'  here        = x∈ys
  aux p' (there z∈xs) = p' z∈xs

reduce : ∀ {α} {A : Set α} {x : A} {xs} -> x ∈ xs -> List A
reduce {xs = x ∷ xs}  here        = xs
reduce {xs = x ∷ xs} (there x∈xs) = x ∷ reduce x∈xs

bubble : ∀ {α} {A : Set α} {x} {xs ys : List A}
       -> x ∷ xs ⊆ ys -> (x∈ys : x ∈ ys) -> x ∷ xs ⊆ x ∷ reduce x∈ys
bubble         p  here        z∈x∷xs = p z∈x∷xs
bubble {x = x} p (there x∈ys) z∈x∷xs with p z∈x∷xs
... | here       = there here
... | there z∈ys = swap $ there $ bubble aux x∈ys $ there z∈ys where
  aux : x ∷ _ ⊆ _
  aux  here        = x∈ys
  aux (there z∈xs) = z∈xs

reduce-length : ∀ {α} {A : Set α} {x} {xs : List A}
              -> (x∈xs : x ∈ xs)
              -> (ys : List A)
              -> length xs ≤ length ys
              -> length (reduce x∈xs) < length ys
reduce-length  here         ys       le      = le
reduce-length (there x∈xs)  []       ()
reduce-length (there x∈xs) (_ ∷ ys) (s≤s le) = s≤s (reduce-length x∈xs ys le)

pigeonhole : ∀ {α} {A : Set α}
           -> (xs ys : List A) -> xs ⊆ ys -> length xs > length ys -> repeats xs
pigeonhole  []      ys p  ()
pigeonhole (x ∷ xs) ys p (s≤s gt) with cut (bubble p (p here))
... | inj₁ x∈xs = this x∈xs
... | inj₂ p'   = other (pigeonhole xs (reduce (p here)) p'
                          (reduce-length (p here) xs gt))
