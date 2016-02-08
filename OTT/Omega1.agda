{-# OPTIONS --no-positivity-check --no-termination-check #-}

open import Function
open import Data.Empty
open import Data.Unit.Base using (⊤; tt)
open import Data.Bool.Base using (Bool; true; false; _∨_)
open import Data.Nat.Base renaming (_⊔_ to _⊔ℕ_)
open import Data.Product

infixl 7 _⊔[_]ᵢ_ _⊔[_]_
infixl 7 _&_
infixr 5 _⇒_

data Lev : Bool -> Set where
  #  : ∀ {a} -> ℕ -> Lev a
  ω₀ : ∀ {a} -> Lev a
  ω₁ : Lev true

isInf : ∀ {a} -> Lev a -> Bool
isInf (# α) = false
isInf  _    = true

lsuc : (α : Lev false) -> Lev (isInf α)
lsuc (# α) = # (suc α)
lsuc  ω₀   = ω₁

data Lsuc : ∀ {b} -> Lev false -> Lev b -> Set where
  l#  : ∀ {b} α -> Lsuc {b} (# α) (# (suc α))
  lω₀ : Lsuc ω₀ ω₁

toSuc : (α : Lev false) -> Lsuc α (lsuc α)
toSuc (# α) = l# α
toSuc  ω₀   = lω₀

data Or : Bool -> Bool -> Bool -> Set where
  t∨ : ∀ {a} -> Or true  a true
  f∨ : ∀ {b} -> Or false b b

toOr : ∀ a b -> Or a b (a ∨ b)
toOr true  b = t∨
toOr false b = f∨

orLev : ∀ {a b c} -> Or a b c -> Lev b -> Lev c
orLev o  (# α) = # α
orLev o   ω₀   = ω₀
orLev t∨  ω₁   = ω₁
orLev f∨  ω₁   = ω₁

_⊔[_]_ : ∀ {a b c} -> Lev a -> Or a b c -> Lev b -> Lev c
# α ⊔[ o  ] # β = # (α ⊔ℕ β)
ω₀  ⊔[ o  ] # _ = ω₀
ω₁  ⊔[ t∨ ] _   = ω₁
_   ⊔[ o  ] β   = orLev o β

_⊔[_]ᵢ_ : ∀ {a b c} -> Lev a -> Or a b c -> Lev b -> Lev c
α ⊔[ o ]ᵢ # 0 = # 0
α ⊔[ o ]ᵢ β   = α ⊔[ o ] β

mutual
  Prop  = ∀ {a} -> Univ {a} (# 0)
  Type⁺ = Univ ∘ lsuc
  Type  = Type⁺ ∘ #

  data Univ : ∀ {a} -> Lev a -> Set where
    bot top : Prop
    nat lev : Type 0
    luniv   : ∀ {b} {β : Lev b} α -> Lsuc α β -> Univ β
    σ′      : ∀ {a b c} {α : Lev a} {β : Lev b} {o : Or a b c}
            -> (A : Univ α) -> (⟦ A ⟧ -> Univ β) -> Univ (α ⊔[ o ]  β)
    π′      : ∀ {a b c} {α : Lev a} {β : Lev b} {o : Or a b c}
            -> (A : Univ α) -> (⟦ A ⟧ -> Univ β) -> Univ (α ⊔[ o ]ᵢ β)
    σ₀ π₀   : {α : Lev false}
            -> (A : Univ α) {k : ⟦ A ⟧ -> Lev false} -> (∀ x -> Univ (k x)) -> Univ {false} ω₀
    σ₁ π₁   : ∀ {a} {α : Lev a}
            -> (A : Univ α) {b : ⟦ A ⟧ -> Bool} {k : ∀ x -> Lev (b x)}
            -> (∀ x -> Univ (k x))
            -> Univ ω₁

  ⟦_⟧ : ∀ {a} {α : Lev a} -> Univ α -> Set
  ⟦ bot       ⟧ = ⊥
  ⟦ top       ⟧ = ⊤
  ⟦ nat       ⟧ = ℕ
  ⟦ lev       ⟧ = Lev false
  ⟦ luniv α s ⟧ = Univ α
  ⟦ σ′ A B    ⟧ = Σ ⟦ A ⟧ λ x -> ⟦ B x ⟧
  ⟦ π′ A B    ⟧ = (x : ⟦ A ⟧) -> ⟦ B x ⟧
  ⟦ σ₀ A B    ⟧ = Σ ⟦ A ⟧ λ x -> ⟦ B x ⟧
  ⟦ π₀ A B    ⟧ = (x : ⟦ A ⟧) -> ⟦ B x ⟧
  ⟦ σ₁ A B    ⟧ = Σ ⟦ A ⟧ λ x -> ⟦ B x ⟧
  ⟦ π₁ A B    ⟧ = (x : ⟦ A ⟧) -> ⟦ B x ⟧

pattern puniv α = luniv _ (l# α)
pattern σᶠ A B  = σ′ {o = f∨} A B
pattern πᶠ A B  = π′ {o = f∨} A B

univ⁺ : ∀ α -> Type⁺ α
univ⁺ α = luniv α (toSuc α)

univ = univ⁺ ∘ #
prop = univ 0
type = univ ∘ suc

σ : ∀ {a b} {α : Lev a} {β : Lev b}
  -> (A : Univ α) -> (⟦ A ⟧ -> Univ β) -> Univ (α ⊔[ toOr a b ]  β)
σ = σ′

π : ∀ {a b} {α : Lev a} {β : Lev b}
  -> (A : Univ α) -> (⟦ A ⟧ -> Univ β) -> Univ (α ⊔[ toOr a b ]ᵢ β)
π = π′

_&_ : ∀ {a b} {α : Lev a} {β : Lev b} -> Univ α -> Univ β -> Univ (α ⊔[ toOr a b ]  β)
A & B = σ A λ _ -> B

_⇒_ : ∀ {a b} {α : Lev a} {β : Lev b} -> Univ α -> Univ β -> Univ (α ⊔[ toOr a b ]ᵢ β)
A ⇒ B = π A λ _ -> B

--------------------

_≟ℕ_ : ⟦ nat ⇒ nat ⇒ prop ⟧
0     ≟ℕ 0     = top
suc n ≟ℕ suc m = n ≟ℕ m
_     ≟ℕ _     = bot

_≟L_ : ⟦ lev ⇒ lev ⇒ prop ⟧
# α ≟L # β = α ≟ℕ β
ω₀  ≟L ω₀  = top
_   ≟L _   = bot

mutual
  Eq : ⟦ (π₁ lev λ α -> π₁ lev λ β -> univ⁺ α ⇒ univ⁺ β ⇒ prop) ⟧
  Eq _ _  bot        bot       = top
  Eq _ _  top        top       = top
  Eq _ _  nat        nat       = top
  Eq _ _  lev        lev       = top
  Eq _ _ (puniv α₁) (puniv α₂) = α₁ ≟ℕ α₂
  Eq _ _ (σᶠ A₁ B₁) (σᶠ A₂ B₂) =
    Eq _ _ A₁ A₂ & π A₁ λ x₁ -> π A₂ λ x₂ -> eq _ _ A₁ A₂ x₁ x₂ ⇒ Eq _ _ (B₁ x₁) (B₂ x₂)
  Eq _ _ (πᶠ A₁ B₁) (πᶠ A₂ B₂) =
    Eq _ _ A₂ A₁ & π A₁ λ x₁ -> π A₂ λ x₂ -> eq _ _ A₂ A₁ x₂ x₁ ⇒ Eq _ _ (B₁ x₁) (B₂ x₂)
  Eq _ _ (σ₀ A₁ B₁) (σ₀ A₂ B₂) =
    Eq _ _ A₁ A₂ & π A₁ λ x₁ -> π A₂ λ x₂ -> eq _ _ A₁ A₂ x₁ x₂ ⇒ Eq _ _ (B₁ x₁) (B₂ x₂)
  Eq _ _ (π₀ A₁ B₁) (π₀ A₂ B₂) =
    Eq _ _ A₂ A₁ & π A₁ λ x₁ -> π A₂ λ x₂ -> eq _ _ A₂ A₁ x₂ x₁ ⇒ Eq _ _ (B₁ x₁) (B₂ x₂)
  Eq _ _  _          _         = bot

  eq : ⟦ (π₁ lev λ α -> π₁ lev λ β -> π (univ⁺ α) λ A -> π (univ⁺ β) λ B -> A ⇒ B ⇒ prop) ⟧
  eq _ _  bot        bot       () ()
  eq _ _  top        top       tt tt = top
  eq _ _  nat        nat       n₁ n₂ = n₁ ≟ℕ n₂
  eq _ _  lev        lev       α₁ α₂ = α₁ ≟L α₂
  eq _ _ (puniv α₁) (puniv α₂) A₁ A₂ = Eq _ _ A₁ A₂
  eq _ _ (σᶠ A₁ B₁) (σᶠ A₂ B₂) p₁ p₂ = let x₁ , y₁ = p₁ ; x₂ , y₂ = p₂ in
    eq _ _ A₁ A₂ x₁ x₂ & eq _ _ (B₁ x₁) (B₂ x₂) y₁ y₂
  eq _ _ (πᶠ A₁ B₁) (πᶠ A₂ B₂) f₁ f₂ =
    π A₁ λ x₁ -> π A₂ λ x₂ -> eq _ _ A₁ A₂ x₁ x₂ ⇒ eq _ _ (B₁ x₁) (B₂ x₂) (f₁ x₁) (f₂ x₂)
  eq _ _ (σ₀ A₁ B₁) (σ₀ A₂ B₂) p₁ p₂ = let x₁ , y₁ = p₁ ; x₂ , y₂ = p₂ in
    eq _ _ A₁ A₂ x₁ x₂ & eq _ _ (B₁ x₁) (B₂ x₂) y₁ y₂
  eq _ _ (π₀ A₁ B₁) (π₀ A₂ B₂) f₁ f₂ =
    π A₁ λ x₁ -> π A₂ λ x₂ -> eq _ _ A₁ A₂ x₁ x₂ ⇒ eq _ _ (B₁ x₁) (B₂ x₂) (f₁ x₁) (f₂ x₂)
  eq _ _  _          _         _  _  = bot

Coerceᵏ : ⟦ (π₀ (nat ⇒ nat) λ k -> π₀ nat λ α -> π₀ nat λ β ->
               α ≟ℕ β ⇒ univ (k α) ⇒ univ (k β)) ⟧
Coerceᵏ k  0       0      r  A = A
Coerceᵏ k (suc n) (suc m) r  A = Coerceᵏ (k ∘ suc) n m r A 
Coerceᵏ k  0      (suc m) () A
Coerceᵏ k (suc n)  0      () A

Coerce : ⟦ (π₀ nat λ α -> π₀ nat λ β -> α ≟ℕ β ⇒ univ α ⇒ univ β) ⟧
Coerce = Coerceᵏ id

mutual
  coerce : ⟦ (π₁ lev λ α -> π₁ lev λ β -> π (univ⁺ α) λ A -> π (univ⁺ β) λ B -> Eq _ _ A B ⇒ A ⇒ B) ⟧
  coerce _ _  bot        bot       r ()
  coerce _ _  top        top       r tt = tt
  coerce _ _  nat        nat       r n  = n
  coerce _ _  lev        lev       r α  = α
  coerce _ _ (puniv α₁) (puniv α₂) r A  = Coerce _ _ r A
  coerce _ _ (σᶠ A₁ B₁) (σᶠ A₂ B₂) r p  =
    let r₁ , r₂ = r ; x , y = p ; x′ = coerce _ _ A₁ A₂ r₁ x in
      x′ , coerce _ _ (B₁ x) (B₂ x′) (r₂ x x′ (coherence _ _ A₁ A₂ r₁ x)) y
  coerce _ _ (πᶠ A₁ B₁) (πᶠ A₂ B₂) r f  =
    λ x -> let r₁ , r₂ = r ; x′ = coerce _ _ A₂ A₁ r₁ x in
      coerce _ _ (B₁ x′) (B₂ x) (r₂ x′ x (coherence _ _ A₂ A₁ r₁ x)) (f x′)
  coerce _ _ (σ₀ A₁ B₁) (σ₀ A₂ B₂) r p  =
    let r₁ , r₂ = r ; x , y = p ; x′ = coerce _ _ A₁ A₂ r₁ x in
      x′ , coerce _ _ (B₁ x) (B₂ x′) (r₂ x x′ (coherence _ _ A₁ A₂ r₁ x)) y
  coerce _ _ (π₀ A₁ B₁) (π₀ A₂ B₂) r f  =
    λ x -> let r₁ , r₂ = r ; x′ = coerce _ _ A₂ A₁ r₁ x in
      coerce _ _ (B₁ x′) (B₂ x) (r₂ x′ x (coherence _ _ A₂ A₁ r₁ x)) (f x′)
  coerce _ _  bot       top      ()
  coerce _ _  bot       nat      ()
  coerce _ _  bot       lev      ()
  coerce _ _  bot      (puniv _) ()
  coerce _ _  bot      (σᶠ _ _)  ()
  coerce _ _  bot      (πᶠ _ _)  ()
  coerce _ _  bot      (σ₀ _ _)  ()
  coerce _ _  bot      (π₀ _ _)  ()
  coerce _ _  top       bot      ()
  coerce _ _  top       nat      ()
  coerce _ _  top       lev      ()
  coerce _ _  top      (puniv _) ()
  coerce _ _  top      (σᶠ _ _)  ()
  coerce _ _  top      (πᶠ _ _)  ()
  coerce _ _  top      (σ₀ _ _)  ()
  coerce _ _  top      (π₀ _ _)  ()
  coerce _ _  nat       bot      ()
  coerce _ _  nat       top      ()
  coerce _ _  nat       lev      ()
  coerce _ _  nat      (puniv _) ()
  coerce _ _  nat      (σᶠ _ _)  ()
  coerce _ _  nat      (πᶠ _ _)  ()
  coerce _ _  nat      (σ₀ _ _)  ()
  coerce _ _  nat      (π₀ _ _)  ()
  coerce _ _  lev       bot      ()
  coerce _ _  lev       top      ()
  coerce _ _  lev       nat      ()
  coerce _ _  lev      (puniv _) ()
  coerce _ _  lev      (σᶠ _ _)  ()
  coerce _ _  lev      (πᶠ _ _)  ()
  coerce _ _  lev      (σ₀ _ _)  ()
  coerce _ _  lev      (π₀ _ _)  ()
  coerce _ _ (puniv _)  bot      ()
  coerce _ _ (puniv _)  top      ()
  coerce _ _ (puniv _)  nat      ()
  coerce _ _ (puniv _)  lev      ()
  coerce _ _ (puniv _) (σᶠ _ _)  ()
  coerce _ _ (puniv _) (πᶠ _ _)  ()
  coerce _ _ (puniv _) (σ₀ _ _)  ()
  coerce _ _ (puniv _) (π₀ _ _)  ()
  coerce _ _ (σᶠ _ _)   bot      ()
  coerce _ _ (σᶠ _ _)   top      ()
  coerce _ _ (σᶠ _ _)   nat      ()
  coerce _ _ (σᶠ _ _)   lev      ()
  coerce _ _ (σᶠ _ _)  (puniv _) ()
  coerce _ _ (σᶠ _ _)  (πᶠ _ _)  ()
  coerce _ _ (σᶠ _ _)  (σ₀ _ _)  ()
  coerce _ _ (σᶠ _ _)  (π₀ _ _)  ()
  coerce _ _ (πᶠ _ _)   bot      ()
  coerce _ _ (πᶠ _ _)   top      ()
  coerce _ _ (πᶠ _ _)   nat      ()
  coerce _ _ (πᶠ _ _)   lev      ()
  coerce _ _ (πᶠ _ _)  (puniv _) ()
  coerce _ _ (πᶠ _ _)  (σᶠ _ _)  ()
  coerce _ _ (πᶠ _ _)  (σ₀ _ _)  ()
  coerce _ _ (πᶠ _ _)  (π₀ _ _)  ()
  coerce _ _ (σ₀ _ _)   bot      ()
  coerce _ _ (σ₀ _ _)   top      ()
  coerce _ _ (σ₀ _ _)   nat      ()
  coerce _ _ (σ₀ _ _)   lev      ()
  coerce _ _ (σ₀ _ _)  (puniv _) ()
  coerce _ _ (σ₀ _ _)  (σᶠ _ _)  ()
  coerce _ _ (σ₀ _ _)  (πᶠ _ _)  ()
  coerce _ _ (σ₀ _ _)  (π₀ _ _)  ()
  coerce _ _ (π₀ _ _)   bot      ()
  coerce _ _ (π₀ _ _)   top      ()
  coerce _ _ (π₀ _ _)   nat      ()
  coerce _ _ (π₀ _ _)   lev      ()
  coerce _ _ (π₀ _ _)  (puniv _) ()
  coerce _ _ (π₀ _ _)  (σᶠ _ _)  ()
  coerce _ _ (π₀ _ _)  (πᶠ _ _)  ()
  coerce _ _ (π₀ _ _)  (σ₀ _ _)  ()
  -- Was generated by http://ideone.com/C3OPpi

  postulate
    coherence : ⟦ (π₁ lev λ α -> π₁ lev λ β -> π (univ⁺ α) λ A -> π (univ⁺ β) λ B -> 
                     π (Eq _ _ A B) λ r -> π A λ x -> eq _ _ A B x (coerce _ _ A B r x)) ⟧

postulate
  refl : ⟦ (π₁ lev λ α -> π (univ⁺ α) λ A -> π A λ x -> eq _ _ A A x x) ⟧
  cong-levOf : ⟦ (π₀ nat λ α -> π₀ nat λ β ->
                    π (univ α) λ A -> π (univ β) λ B -> Eq _ _ A B ⇒ α ≟ℕ β) ⟧

cong : ⟦ (π₁ lev λ α -> π₁ lev λ β -> π (univ⁺ α) λ A ->
            π (A ⇒ univ⁺ β) λ B -> π A λ x -> π A λ y -> π (π A B) λ f ->
              eq _ _ A A x y ⇒ eq _ _ (B x) (B y) (f x) (f y)) ⟧
cong α β A B x y f r = refl _ (π A B) f x y r

hsubstitutive : ⟦ (π₀ nat λ α -> π₀ nat λ β -> π₀ nat λ δ ->
                     π (univ α) λ A -> π (univ β) λ B -> π A λ x -> π B λ y ->
                       π (π₀ nat λ γ -> π (univ γ) λ C -> C ⇒ univ δ) λ D ->
                         Eq _ _ A B ⇒ eq _ _ A B x y ⇒ Eq _ _ (D _ A x) (D _ B y)) ⟧
hsubstitutive α β δ A B x y D r q =
  refl _ (π₀ nat λ γ -> π (univ γ) λ C -> C ⇒ univ δ) D _ _ (cong-levOf _ _ A B r) A B r x y q

cong-≅z : ⟦ (π₀ nat λ α -> π₀ nat λ β -> π₀ nat λ γ ->
               π (univ α) λ A -> π (univ β) λ B -> π (univ γ) λ C ->
                 π A λ x -> π B λ y -> π C λ z -> Eq _ _ A B ⇒
                   eq _ _ A B x y ⇒ Eq _ _ (eq _ _ A C x z) (eq _ _ B C y z)) ⟧
cong-≅z α β γ A B C x y z r q = hsubstitutive _ _ _ A B x y (λ _ C' z' -> eq _ _ C' C z' z) r q

right : ⟦ (π₀ nat λ α -> π₀ nat λ β -> π₀ nat λ γ ->
             π (univ α) λ A -> π (univ β) λ B -> π (univ γ) λ C ->
               π A λ x -> π B λ y -> π C λ z -> Eq _ _ A B ⇒
                 eq _ _ A B x y ⇒ eq _ _ A C x z ⇒ eq _ _ B C y z) ⟧
right α β γ A B C x y z r q₁ q₂ =
  coerce _ _ (eq _ _ A C x z) (eq _ _ B C y z) (cong-≅z _ _ _ A B C x y z r q₁) q₂

sym : ⟦ (π₀ nat λ α -> π₀ nat λ β -> π (univ α) λ A -> π (univ β) λ B ->
           π A λ x -> π B λ y -> Eq _ _ A B ⇒ eq _ _ A B x y ⇒ eq _ _ B A y x) ⟧
sym α β A B x y r q = right _ _ _ A B A x y x r q (refl _ A x) 

sym-prop : ⟦ (π prop λ A -> π prop λ B -> Eq _ _ A B ⇒ Eq _ _ B A) ⟧
sym-prop A B r = sym _ _ prop prop A B tt r

trans : ⟦ (π₀ nat λ α -> π₀ nat λ β -> π₀ nat λ γ ->
             π (univ α) λ A -> π (univ β) λ B -> π (univ γ) λ C ->
               π A λ x -> π B λ y -> π C λ z -> Eq _ _ A B ⇒
                 eq _ _ A B x y ⇒ eq _ _ B C y z ⇒ eq _ _ A C x z) ⟧
trans α β γ A B C x y z r q₁ q₂ =
  coerce _ _ (eq _ _ B C y z) (eq _ _ A C x z)
    (sym-prop (eq _ _ A C x z) (eq _ _ B C y z) (cong-≅z _ _ _ A B C x y z r q₁)) q₂

trans-prop : ⟦ (π prop λ A -> π prop λ B -> π prop λ C -> Eq _ _ A B ⇒ Eq _ _ B C ⇒ Eq _ _ A C) ⟧
trans-prop A B C r q = trans _ _ _ prop prop prop A B C tt r q
