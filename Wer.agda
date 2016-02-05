{-# OPTIONS --type-in-type #-}

Effect : Set -> Set
Effect R = R -> (A : Set) -> (A -> R) -> Set

data Wer {R} (Ψ : Effect R) : Effect R where
  call : ∀ {r A r′ B r′′} -> Ψ r A r′ -> (∀ x -> Wer Ψ (r′ x) B r′′) -> Wer Ψ r B r′′

elimWer : ∀ {R r A r′} {Ψ : Effect R}
        -> (P : ∀ {r A r′} -> Wer Ψ r A r′ -> Set)
        -> (∀ {r A r′ B r′′}
            -> (a : Ψ r A r′)
            -> (k : ∀ x -> Wer Ψ (r′ x) B r′′)
            -> (∀ x -> P (k x))
            -> P (call a k))
        -> (w : Wer Ψ r A r′)
        -> P w
elimWer P f (call a k) = f a k (λ x -> elimWer P f (k x))



open import Function
open import Data.Empty
open import Data.Unit.Base
open import Data.Bool.Base
open import Data.Nat.Base as Nat hiding (fold)
open import Data.Fin             hiding (fold)
open import Data.Product
open import Data.Vec hiding (_∈_)

infixr 5 _<∨>_

_<∨>_ : ∀ {B : Bool -> Set} -> B true -> B false -> ∀ b -> B b
(x <∨> y) true  = x
(x <∨> y) false = y

infixr 6 _⇒_
infixl 5 _▻_
infix  3 _∈_ _⊢_
infixr 4 vs_
infixr 0 ƛ_
infixl 6 _·_

data Type : Set where
  nat : Type
  _⇒_ : Type -> Type -> Type

⟦_⟧ : Type -> Set
⟦ nat   ⟧ = ℕ
⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ -> ⟦ τ ⟧

data Con : Set where
  ε   : Con
  _▻_ : Con -> Type -> Con

data _∈_ σ : Con -> Set where
  vz  : ∀ {Γ}   -> σ ∈ Γ ▻ σ
  vs_ : ∀ {Γ τ} -> σ ∈ Γ     -> σ ∈ Γ ▻ τ

data Env : Con -> Set where
  ∅   : Env ε
  _▷_ : ∀ {Γ σ} -> Env Γ -> ⟦ σ ⟧ -> Env (Γ ▻ σ)

lookupᵉ : ∀ {Γ σ} -> σ ∈ Γ -> Env Γ -> ⟦ σ ⟧
lookupᵉ  vz    (ρ ▷ x) = x
lookupᵉ (vs v) (ρ ▷ x) = lookupᵉ v ρ

app-arg : Bool -> Type -> Type -> Type
app-arg b σ τ = if b then σ ⇒ τ else σ

fold-arg : Fin 3 -> Type -> Type
fold-arg i σ = lookup i (σ ⇒ σ ∷ σ ∷ nat ∷ [])

data TermE : Effect (Con × Type) where
  Pure  : ∀ {Γ σ  } -> ⟦ σ ⟧ -> TermE (Γ , σ    )  ⊥       λ()
  Var   : ∀ {Γ σ  } -> σ ∈ Γ -> TermE (Γ , σ    )  ⊥       λ()
  Lam   : ∀ {Γ σ τ} ->          TermE (Γ , σ ⇒ τ)  ⊤      (λ _ -> Γ ▻ σ , τ            )
  App   : ∀ {Γ σ τ} ->          TermE (Γ , τ    )  Bool   (λ b -> Γ     , app-arg b σ τ)
  Z     : ∀ {Γ    } ->          TermE (Γ , nat  )  ⊥       λ()
  S     : ∀ {Γ    } ->          TermE (Γ , nat  )  ⊤      (λ _ -> Γ     , nat          )
  Fold  : ∀ {Γ σ  } ->          TermE (Γ , σ    ) (Fin 3) (λ i -> Γ     , fold-arg i σ )

_⊢_ : Con -> Type -> Set
Γ ⊢ σ = Wer TermE (Γ , σ) ⊥ λ()

Term⁺ : Type -> Set
Term⁺ σ = ∀ {Γ} -> Γ ⊢ σ

Term⁽⁾ : Type -> Set
Term⁽⁾ σ = ε ⊢ σ

pure : ∀ {Γ σ} -> ⟦ σ ⟧ -> Γ ⊢ σ
pure x = call (Pure x) λ()

var : ∀ {Γ σ} -> σ ∈ Γ -> Γ ⊢ σ
var v = call (Var v) λ()

ƛ_ : ∀ {Γ σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
ƛ b = call Lam (const b)

_·_ : ∀ {Γ σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ -> Γ ⊢ τ
f · x = call App (f <∨> x)

z : ∀ {Γ} -> Γ ⊢ nat
z = call Z λ()

s : ∀ {Γ} -> Γ ⊢ nat -> Γ ⊢ nat
s n = call S (const n)

fold : ∀ {Γ σ} -> Γ ⊢ σ ⇒ σ -> Γ ⊢ σ -> Γ ⊢ nat -> Γ ⊢ σ
fold f z n = call Fold k where
  k : (i : Fin 3) -> _
  k  zero                = f
  k (suc  zero)          = z
  k (suc (suc  zero))    = n
  k (suc (suc (suc ())))

⟦_⟧ᵥ : ∀ {Γ σ} -> Γ ⊢ σ -> Env Γ -> ⟦ σ ⟧
⟦ call (Pure x) k ⟧ᵥ ρ = x
⟦ call (Var v)  k ⟧ᵥ ρ = lookupᵉ v ρ
⟦ call  Lam     k ⟧ᵥ ρ = λ x -> ⟦ k tt ⟧ᵥ (ρ ▷ x)
⟦ call  App     k ⟧ᵥ ρ = ⟦ k true ⟧ᵥ ρ (⟦ k false ⟧ᵥ ρ) 
⟦ call  Z       k ⟧ᵥ ρ = 0
⟦ call  S       k ⟧ᵥ ρ = suc (⟦ k tt ⟧ᵥ ρ)
⟦ call  Fold    k ⟧ᵥ ρ = Nat.fold (⟦ k (suc zero) ⟧ᵥ ρ) (⟦ k zero ⟧ᵥ ρ) (⟦ k (suc (suc zero)) ⟧ᵥ ρ)

eval : ∀ {σ} -> Term⁽⁾ σ -> ⟦ σ ⟧
eval t = ⟦ t ⟧ᵥ ∅



open import Relation.Binary.PropositionalEquality

A : ∀ {σ τ} -> Term⁺ ((σ ⇒ τ) ⇒ σ ⇒ τ)
A = ƛ ƛ var (vs vz) · var vz

test : ∀ {σ τ} -> eval (A {σ} {τ}) ≡ _$_
test = refl
