open import Data.Nat
open import Data.Fin

infixl 2 _,_
infixr 2 _Π_
infix  1 _⊢_ _≈_
infix  2 _[_]

infix  1 ƛ_
infix  2 pop_
infixl 4 _·_

predⁿ : ∀ n -> Fin n -> ℕ
predⁿ (suc n)  zero   = n
predⁿ (suc n) (suc i) = suc (predⁿ n i)

{-# TERMINATING #-}
mutual
  data Con : ℕ -> Set where
    ε : Con 0
    _,_ : ∀ {n} (Γ : Con n) -> Type Γ -> Con (suc n)

  data Type : ∀ {n} -> Con n -> Set where
    type : ∀ {n} {Γ : Con n} -> Type Γ
    _Π_  : ∀ {n} {Γ : Con n} -> (σ : Type Γ) -> Type (Γ , σ) -> Type Γ
    ↑    : ∀ {n} {Γ : Con n} -> Γ ⊢ type     -> Type Γ

  data _⊢_ : ∀ {n} (Γ : Con n) -> Type Γ -> Set where
    ƛ_   : ∀ {n} {Γ : Con n} {σ τ} -> Γ , σ ⊢ τ     -> Γ ⊢ σ Π τ
    _·_  : ∀ {n} {Γ : Con n} {σ τ} -> Γ ⊢ σ Π τ     -> (x : Γ ⊢ σ)   -> Γ ⊢ τ [ x ]
    ↓    : ∀ {n} {Γ : Con n}       -> Type Γ        -> Γ ⊢ type
    top  : ∀ {n} {Γ : Con n} {σ}   -> Γ , σ ⊢ Pop σ
    pop_ : ∀ {n} {Γ : Con n} {σ τ} -> Γ ⊢ τ         -> Γ , σ ⊢ Pop τ
    coe  : ∀ {n} {Γ : Con n} {σ τ} -> Γ ⊢ σ         -> .(σ ≈ τ)      -> Γ ⊢ τ

  rdrop : ∀ {n} i -> Con n -> Con (n ℕ-ℕ i)
  rdrop  zero     Γ      = Γ
  rdrop (suc ())  ε
  rdrop (suc n)  (Γ , σ) = rdrop n Γ

  rlookup : ∀ {n} i (Γ : Con n) -> Type (rdrop (suc i) Γ)
  rlookup  zero   (Γ , σ) = σ
  rlookup (suc i) (Γ , σ) = rlookup i Γ

  rinsert : ∀ {n} i (Γ : Con n) -> Type (rdrop i Γ) -> Con (suc n)
  rinsert  zero     Γ      τ = Γ , τ
  rinsert (suc ())  ε      τ
  rinsert (suc i)  (Γ , σ) τ = rinsert i Γ τ , Weaken i σ

  Weaken : ∀ {n} i {Γ : Con n} {σ} -> Type Γ -> Type (rinsert i Γ σ)
  Weaken i  type   = type
  Weaken i (σ Π τ) = Weaken i σ Π Weaken (suc i) τ
  Weaken i (↑ t)   = ↑ (weaken i t)

  Pop : ∀ {n} {Γ : Con n} {σ} -> Type Γ -> Type _
  Pop {σ = σ} = Weaken zero {σ = σ}

  inst : ∀ {n} i (Γ : Con n) -> rdrop (suc i) Γ ⊢ rlookup i Γ -> Con (predⁿ n i)
  inst  zero   (Γ , σ) x = Γ
  inst (suc i) (Γ , σ) x = inst i Γ x , Subst i σ x

  Subst : ∀ {n} i {Γ : Con n}
        -> Type Γ -> (x : rdrop (suc i) Γ ⊢ rlookup i Γ) -> Type (inst i Γ x)
  Subst i  type   x = type
  Subst i (σ Π τ) x = Subst i σ x Π Subst (suc i) τ x
  Subst i (↑ t)   x = ↑ (subst i t x)

  _[_] : ∀ {n} {Γ : Con n} {σ} -> Type _ -> Γ ⊢ σ -> Type Γ
  _[_] = Subst zero

  data _≈_ : ∀ {n} {Γ Δ : Con n} -> Type Γ -> Type Δ -> Set where
    Weaken-Pop     : ∀ {n i} {Γ : Con n} {σ   : Type Γ} {τ υ}
                   -> Pop (Weaken i σ) ≈ Weaken (suc i) {σ = υ} (Pop {σ = τ} σ)
    Pop-[]ᵀ        : ∀ {n}   {Γ : Con n} {σ   : Type Γ} {τ x}
                   -> σ ≈ Pop {σ = τ} σ [ x ]
    swap-Pop-Subst : ∀ {n i} {Γ : Con n} {σ   : Type Γ} {x τ υ}
                   -> Pop {σ = υ} (Subst i σ x) ≈ Subst (suc i) (Pop {σ = τ} σ) x
    fold-Weaken    : ∀ {n i} {Γ : Con n} {σ   : Type Γ} {x τ υ}
                   -> Weaken (suc i) {σ = υ} τ [ weaken i {τ = σ} x ] ≈ Weaken i {σ = υ} (τ [ x ])
    fold-Subst     : ∀ {n i} {Γ : Con n} {σ   : Type Γ} {x τ} {y : Γ ⊢ σ}
                   -> Subst (suc i) τ x [ subst i y x ] ≈ Subst i (τ [ y ]) x
    cong-Weaken    : ∀ {n i} {Γ : Con n} {σ τ : Type Γ} {υ}
                   -> σ ≈ τ -> Weaken i {σ = υ} σ ≈ Weaken i τ
    cong-Subst     : ∀ {n i} {Γ : Con n} {σ τ : Type Γ} {x}
                   -> σ ≈ τ -> Subst i σ x ≈ Subst i τ x

  weaken : ∀ {n} i {Γ : Con n} {σ τ} -> Γ ⊢ τ -> rinsert i Γ σ ⊢ Weaken i τ
  weaken  i      (ƛ b)     = ƛ (weaken (suc i) b)
  weaken  i      (f · x)   = coe (weaken i f · weaken i x) fold-Weaken
  weaken  i      (↓ σ)     = ↓ (Weaken i σ)
  weaken  zero    x        = pop  x
  weaken (suc i)  top      = coe  top                Weaken-Pop
  weaken (suc i) (pop x)   = coe (pop (weaken i x))  Weaken-Pop
  weaken  i      (coe x r) = coe      (weaken i x)  (cong-Weaken r)

  subst : ∀ {n} i {Γ : Con n} {τ}
        -> Γ ⊢ τ  -> (x : rdrop (suc i) Γ ⊢ rlookup i Γ) -> inst i Γ x ⊢ Subst i τ x
  subst  i      (ƛ b)     x = ƛ (subst (suc i) b x)
  subst  i      (f · y)   x = coe (subst i f x · subst i y x) fold-Subst
  subst  i      (↓ σ)     x = ↓ (Subst i σ x)
  subst  zero    top      x = coe  x                  Pop-[]ᵀ
  subst (suc _)  top      x = coe  top                swap-Pop-Subst
  subst  zero   (pop y)   x = coe  y                  Pop-[]ᵀ
  subst (suc i) (pop y)   x = coe (pop (subst i y x)) swap-Pop-Subst
  subst  i      (coe y r) x = coe      (subst i y x)  (cong-Subst r)

Term : Type ε -> Set
Term σ = ε ⊢ σ

-- Not so terminating. OK, what's going on here?
-- Is it just the Agda's inefficient evaluation strategy?
-- There are no termination issues without the `coe' cases,
-- but Agda consumes more than 1 GB RAM for checking `loop'.
loop : Term ((type Π type) Π type Π type)
loop = ƛ ƛ pop top · top
