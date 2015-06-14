open import Data.List hiding (zipWith)

elimList : ∀ {α γ} {A : Set α}
         -> (C : List A -> Set γ) -> C [] -> (∀ {xs} x -> C xs -> C (x ∷ xs)) -> ∀ xs -> C xs
elimList C z f  []      = z
elimList C z f (x ∷ xs) = f x (elimList C z f xs)

caseList : ∀ {α γ} {A : Set α}
         -> (C : List A -> Set γ) -> C [] -> (∀ x xs -> C (x ∷ xs)) -> ∀ xs -> C xs
caseList C z f = elimList C z (λ {xs} x _ -> f x xs)

zipWith : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ}
        -> (A -> B -> C) -> List A -> List B -> List C
zipWith f = elimList _ (λ ys -> []) (λ x r ys -> caseList _ [] (λ y ys -> f x y ∷ r ys) ys)
