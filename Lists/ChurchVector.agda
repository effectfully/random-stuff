{-# OPTIONS --type-in-type #-}

Nat = ∀ (P : Set) -> (P -> P) -> P -> P

zero : Nat
zero = λ P f z -> z

suc : Nat -> Nat
suc = λ n P f z -> f (n P f z) 

plus : Nat -> Nat -> Nat
plus = λ n m P f z -> n P f (m P f z)

Vec = λ (A : Set) n ->
  (P : Nat -> Set) -> (∀ n -> A -> P n -> P (suc n)) -> P zero -> P n

nil : ∀ A -> Vec A zero
nil = λ A P f z -> z

cons : ∀ A n -> A -> Vec A n -> Vec A (suc n)
cons = λ A n x xs P f z -> f n x (xs P f z)

concat : ∀ A n m -> Vec A n -> Vec A m -> Vec A (plus n m)
concat = λ A n m xs ys P f z -> xs (λ n -> P (plus n m)) (λ n -> f (plus n m)) (ys P f z)

Eq = λ (A : Set) (x y : A) ->
  (P : A -> A -> Set) -> (∀ x -> P x x) -> P x y

refl : ∀ A x -> Eq A x x
refl = λ A x P p -> p x

subst : ∀ A -> (P : A -> Set) -> (x y : A) -> Eq A x y -> P x -> P y
subst = λ A P x y q -> q (λ x y -> P x -> P y) (λ _ p -> p)

tsbus : ∀ A -> (x y : A) -> ((P : A -> Set) -> P x -> P y) -> Eq A x y
tsbus = λ A x y f P r -> f (P x) (r x)

one   = suc zero
two   = suc one
three = suc two

[1] : Vec Nat one
[1] = cons _ _ one (nil _)

[2,3] : Vec Nat two
[2,3] = cons _ _ two (cons _ _ three (nil _))

[1,2,3] : Vec Nat three
[1,2,3] = cons _ _ (suc zero) [2,3]

test1 : Eq _ (concat _ _ _ [1] [2,3]) [1,2,3]
test1 = refl _ _

test2 : Eq _ (plus one two) three
test2 = refl _ _

test3 : ∀ (A : Set) n m -> Eq Nat n m -> Vec A n -> Vec A m
test3 = λ A -> subst Nat (Vec A)
