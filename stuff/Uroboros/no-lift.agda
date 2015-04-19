open import Data.Nat
open import Data.Fin

infixl 2 _,_
infixr 2 _Π_
infix  1 _∋_ _⊢_
infix  2 _[_]ᵀ

predⁿ : ∀ n -> Fin n -> ℕ
predⁿ (suc n)  zero   = n
predⁿ (suc n) (suc i) = suc (predⁿ n i)

mutual
  data Con : ℕ -> Set where
    ε : Con 0
    _,_ : ∀ {n} (Γ : Con n) -> Type Γ -> Con (suc n)

  data Type : ∀ {n} -> Con n -> Set where
    type : ∀ {n} {Γ : Con n} -> Type Γ
    _Π_  : ∀ {n} {Γ : Con n} -> (σ : Type Γ) -> Type (Γ , σ) -> Type Γ

  data _∋_ : ∀ {n} (Γ : Con n) -> Type Γ -> Set where
    vz : ∀ {n} {Γ : Con n} {σ}   -> Γ , σ ∋ Pop σ
    vs : ∀ {n} {Γ : Con n} {σ τ} -> Γ     ∋ σ     -> Γ , τ ∋ Pop σ

  data _⊢_ : ∀ {n} (Γ : Con n) -> Type Γ -> Set where
    ƛ_  : ∀ {n} {Γ : Con n} {σ τ} -> Γ , σ ⊢ τ -> Γ ⊢ σ Π τ
    _·_ : ∀ {n} {Γ : Con n} {σ τ} -> Γ ⊢ σ Π τ -> (x : Γ ⊢ σ) -> Γ ⊢ τ [ x ]ᵀ
    ↓   : ∀ {n} {Γ : Con n}       -> Type Γ    -> Γ ⊢ type
    var : ∀ {n} {Γ : Con n} {σ}   -> Γ ∋ σ    -> Γ ⊢ σ

  rdrop : ∀ {n} i -> Con n -> Con (n ℕ-ℕ i)
  rdrop  zero     Γ      = Γ
  rdrop (suc ())  ε
  rdrop (suc n)  (Γ , σ) = rdrop n Γ

  rinsert : ∀ {n} i (Γ : Con n) -> Type (rdrop i Γ) -> Con (suc n)
  rinsert  zero     Γ      τ = Γ , τ
  rinsert (suc ())  ε      τ
  rinsert (suc i)  (Γ , σ) τ = rinsert i Γ τ , Weaken i σ

  Weaken : ∀ {n} i {Γ : Con n} {σ} -> Type Γ -> Type (rinsert i Γ σ)
  Weaken i  type   = type
  Weaken i (σ Π τ) = Weaken i σ Π Weaken (suc i) τ

  Pop : ∀ {n} {Γ : Con n} {σ} -> Type Γ -> Type _
  Pop {σ = σ} = Weaken zero {σ = σ}

  rlookup : ∀ {n} i (Γ : Con n) -> Type (rdrop (suc i) Γ)
  rlookup  zero   (Γ , σ) = σ
  rlookup (suc i) (Γ , σ) = rlookup i Γ

  inst : ∀ {n} i (Γ : Con n) -> rdrop (suc i) Γ ⊢ rlookup i Γ -> Con (predⁿ n i)
  inst  zero   (Γ , σ) x = Γ
  inst (suc i) (Γ , σ) x = inst i Γ x , Subst i σ x

  Subst : ∀ {n} i {Γ : Con n}
        -> Type Γ -> (x : rdrop (suc i) Γ ⊢ rlookup i Γ) -> Type (inst i Γ x)
  Subst i  type   x = type
  Subst i (σ Π τ) x = Subst i σ x Π Subst (suc i) τ x

  _[_]ᵀ : ∀ {n} {Γ : Con n} {σ} -> Type _ -> Γ ⊢ σ -> Type Γ
  _[_]ᵀ = Subst zero

Top : ∀ {n} {Γ : Con n} {σ} -> Type (Γ , σ)
Top {σ = σ} = Pop σ

Term : Type ε -> Set
Term σ = ε ⊢ σ
