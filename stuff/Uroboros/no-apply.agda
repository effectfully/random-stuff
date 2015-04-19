open import Data.Nat
open import Data.Fin

infixl 2 _,_
infixr 2 _Π_
infix  1 _⊢_
infix  2 _[_]ᵀ

predⁿ : ∀ n -> Fin n -> ℕ
predⁿ (suc n)  zero   = n
predⁿ (suc n) (suc i) = suc (predⁿ n i)

mutual
  data Con : ℕ -> Set where
    ε : Con 0
    _,_ : ∀ {n} (Γ : Con n) -> Type Γ -> Con (suc n)

  data Type : ∀ {n} -> Con n -> Set where
    type : ∀ {n} {Γ : Con n}     -> Type Γ
    _Π_  : ∀ {n} {Γ : Con n}     -> (σ : Type Γ) -> Type (Γ , σ) -> Type Γ
    ↑    : ∀ {n} {Γ : Con n}     -> Γ ⊢ type     -> Type Γ
    Pop_ : ∀ {n} {Γ : Con n} {σ} -> Type Γ       -> Type (Γ , σ)

  data _⊢_ : ∀ {n} (Γ : Con n) -> Type Γ -> Set where
    ƛ_   : ∀ {n} {Γ : Con n} {σ τ} -> Γ , σ ⊢ τ     -> Γ ⊢ σ Π τ
    ↓    : ∀ {n} {Γ : Con n}       -> Type Γ        -> Γ ⊢ type
    top  : ∀ {n} {Γ : Con n} {σ}   -> Γ , σ ⊢ Pop σ
    pop_ : ∀ {n} {Γ : Con n} {σ τ} -> Γ ⊢ τ         -> Γ , σ ⊢ Pop τ

rdrop : ∀ {n} i -> Con n -> Con (n ℕ-ℕ i)
rdrop  zero     Γ      = Γ
rdrop (suc ())  ε
rdrop (suc n)  (Γ , σ) = rdrop n Γ

rlookup : ∀ {n} i (Γ : Con n) -> Type (rdrop (suc i) Γ)
rlookup  zero   (Γ , σ) = σ
rlookup (suc i) (Γ , σ) = rlookup i Γ

mutual
  inst : ∀ {n} i (Γ : Con n) -> rdrop (suc i) Γ ⊢ rlookup i Γ -> Con (predⁿ n i)
  inst  zero   (Γ , σ) x = Γ
  inst (suc i) (Γ , σ) x = inst i Γ x , Subst i σ x

  Subst : ∀ {n} i {Γ : Con n}
        -> Type Γ -> (x : rdrop (suc i) Γ ⊢ rlookup i Γ) -> Type (inst i Γ x)
  Subst  i               type   x = type
  Subst  i              (σ Π τ) x = Subst i σ x Π Subst (suc i) τ x
  Subst  i              (↑ t)   x = ↑ (subst i t x)
  Subst  zero   {_ , _} (Pop σ) x = σ
  Subst (suc i) {_ , _} (Pop σ) x = Pop (Subst i σ x)

  subst : ∀ {n} i {Γ : Con n} {τ}
        -> Γ ⊢ τ  -> (x : rdrop (suc i) Γ ⊢ rlookup i Γ) -> inst i Γ x ⊢ Subst i τ x
  subst  i      (ƛ b)   x = ƛ (subst (suc i) b x)
  subst  i      (↓ σ)   x = ↓ (Subst i σ x)
  subst  zero    top    x = x
  subst (suc _)  top    x = top
  subst  zero   (pop t) x = t
  subst (suc i) (pop t) x = pop (subst i t x)

_[_]ᵀ : ∀ {n} {Γ : Con n} {σ} -> Type (Γ , σ) -> Γ ⊢ σ -> Type Γ
_[_]ᵀ = Subst zero

_[_] : ∀ {n} {Γ : Con n} {σ τ} -> Γ , σ ⊢ τ -> (x : Γ ⊢ σ) -> Γ ⊢ τ [ x ]ᵀ
_[_] = subst zero

_$_ : ∀ {n} {Γ : Con n} {σ τ} -> Γ ⊢ σ Π τ -> (x : Γ ⊢ σ) -> Γ ⊢ τ [ x ]ᵀ
(ƛ b) $ x = b [ x ]

Top : ∀ {n} {Γ : Con n} {σ} -> Type (Γ , σ)
Top {σ = σ} = Pop σ

Term : Type ε -> Set
Term σ = ε ⊢ σ
