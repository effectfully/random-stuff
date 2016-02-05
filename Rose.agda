open import Level renaming (zero to lzero; suc to lsuc)
open import Data.List.Base

infixr 5 _∷₁_ _∷₂_

data List₁ {α β} {A : Set α} (B : A -> Set β) : List A -> Set β where
  []₁  : List₁ B []
  _∷₁_ : ∀ {x xs} -> B x -> List₁ B xs -> List₁ B (x ∷ xs)

data List₂ {α β γ} {A : Set α} {B : A -> Set β} (C : ∀ {x} -> B x -> Set γ)
           : ∀ {xs} -> List₁ B xs -> Set γ where
  []₂  : List₂ C []₁
  _∷₂_ : ∀ {x xs} {y : B x} {ys : List₁ B xs} -> C y -> List₂ C ys -> List₂ C (y ∷₁ ys)

lmap₂ : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : ∀ {x} -> B x -> Set γ} {xs}
      -> (∀ {x} -> (y : B x) -> C y) -> (ys : List₁ B xs) -> List₂ C ys
lmap₂ g  []₁      = []₂
lmap₂ g (y ∷₁ ys) = g y ∷₂ lmap₂ g ys

Over : ∀ {ι} -> Set ι -> ∀ α -> Set (ι ⊔ lsuc α)
Over I α = List I -> I -> Set α

record Rose {ι α} {I : Set ι} (F : Over I α) j : Set (ι ⊔ α) where
  inductive
  constructor rose
  field
    {is}   : List I
    cons   : F is j
    childs : List₁ (Rose F) is

{-# TERMINATING #-}
elimRose : ∀ {ι α π} {I : Set ι} {F : Over I α} {j}
         -> (P : ∀ {j} -> Rose F j -> Set π)
         -> (∀ {is j cs} -> (c : F is j) -> List₂ P cs -> P (rose c cs))
         -> (r : Rose F j)
         -> P r
elimRose P f (rose c cs) = f c (lmap₂ (elimRose P f) cs)



open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Unit.Base
open import Data.Nat.Base
open import Data.Product

module Nat where
  data NatF : Over ⊤ lzero where
    Z : NatF  []       tt
    S : NatF (tt ∷ []) tt

  Nat = Rose NatF tt

  z : Nat
  z = rose Z []₁

  s : Nat -> Nat
  s n = rose S (n ∷₁ []₁)

  elimNat : ∀ {π} -> (P : Nat -> Set π) -> (∀ {n} -> P n -> P (s n)) -> P z -> ∀ n -> P n
  elimNat P f x (rose Z  []₁)       = x
  elimNat P f x (rose S (n ∷₁ []₁)) = f (elimNat P f x n)

  elimNat′ : ∀ {π} -> (P : Nat -> Set π) -> (∀ {n} -> P n -> P (s n)) -> P z -> ∀ n -> P n
  elimNat′ P f x = elimRose P k where
    k : ∀ {is j cs} -> (c : NatF is j) -> List₂ P cs -> P (rose c cs)
    k Z  []₂       = x
    k S (r ∷₂ []₂) = f r

module Vec where
  open Nat

  module VecF {α} (A : Set α) where
    data VecF : Over Nat α where
      Nil  : VecF [] z
      Cons : ∀ {n} -> A -> VecF (n ∷ []) (s n)   
  open VecF

  Vec : ∀ {α} -> Set α -> Nat -> Set α
  Vec A = Rose (VecF A)

  nil : ∀ {α} {A : Set α} -> Vec A z
  nil = rose Nil []₁

  cons : ∀ {n α} {A : Set α} -> A -> Vec A n -> Vec A (s n)
  cons x xs = rose (Cons x) (xs ∷₁ []₁)

  elimVec : ∀ {α π} {A : Set α} {n}
          -> (P : ∀ {n} -> Vec A n -> Set π)
          -> (∀ {n} {xs : Vec A n} x -> P xs -> P (cons x xs))
          -> P nil
          -> (xs : Vec A n)
          -> P xs
  elimVec P f z (rose  Nil      []₁)        = z
  elimVec P f z (rose (Cons x) (xs ∷₁ []₁)) = f x (elimVec P f z xs)

module STLC where
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

  data TermF : Over (Con × Type) lzero where
    Pure  : ∀ {Γ σ  } -> ⟦ σ ⟧ -> TermF  []                                      (Γ , σ    )
    Var   : ∀ {Γ σ  } -> σ ∈ Γ -> TermF  []                                      (Γ , σ    )
    Lam   : ∀ {Γ σ τ} ->          TermF ((Γ ▻ σ , τ) ∷ [])                       (Γ , σ ⇒ τ)
    App   : ∀ {Γ σ τ} ->          TermF ((Γ , σ ⇒ τ) ∷ (Γ , σ) ∷ [])             (Γ , τ    )
    Z     : ∀ {Γ    } ->          TermF  []                                      (Γ , nat  )
    S     : ∀ {Γ    } ->          TermF ((Γ , nat) ∷ [])                         (Γ , nat  )
    Fold  : ∀ {Γ σ  } ->          TermF ((Γ , σ ⇒ σ) ∷ (Γ , σ) ∷ (Γ , nat) ∷ []) (Γ , σ    )
  
  _⊢_ : Con -> Type -> Set
  Γ ⊢ σ = Rose TermF (Γ , σ)

  Term⁺ : Type -> Set
  Term⁺ σ = ∀ {Γ} -> Γ ⊢ σ

  Term⁽⁾ : Type -> Set
  Term⁽⁾ σ = ε ⊢ σ

  pure : ∀ {Γ σ} -> ⟦ σ ⟧ -> Γ ⊢ σ
  pure x = rose (Pure x) []₁

  var : ∀ {Γ σ} -> σ ∈ Γ -> Γ ⊢ σ
  var v = rose (Var v) []₁

  ƛ_ : ∀ {Γ σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  ƛ b = rose Lam (b ∷₁ []₁)

  _·_ : ∀ {Γ σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ -> Γ ⊢ τ
  f · x = rose App (f ∷₁ x ∷₁ []₁)

  z : ∀ {Γ} -> Γ ⊢ nat
  z = rose Z []₁

  s : ∀ {Γ} -> Γ ⊢ nat -> Γ ⊢ nat
  s n = rose S (n ∷₁ []₁)

  tfold : ∀ {Γ σ} -> Γ ⊢ σ ⇒ σ -> Γ ⊢ σ -> Γ ⊢ nat -> Γ ⊢ σ
  tfold f z n = rose Fold (f ∷₁ z ∷₁ n ∷₁ []₁)

  ⟦_⟧ᵥ : ∀ {Γ σ} -> Γ ⊢ σ -> Env Γ -> ⟦ σ ⟧
  ⟦ rose (Pure x)  []₁                 ⟧ᵥ ρ = x
  ⟦ rose (Var v)   []₁                 ⟧ᵥ ρ = lookupᵉ v ρ
  ⟦ rose  Lam     (b ∷₁ []₁)           ⟧ᵥ ρ = λ x -> ⟦ b ⟧ᵥ (ρ ▷ x)
  ⟦ rose  App     (f ∷₁ x ∷₁ []₁)      ⟧ᵥ ρ = ⟦ f ⟧ᵥ ρ (⟦ x ⟧ᵥ ρ)
  ⟦ rose  Z        []₁                 ⟧ᵥ ρ = 0
  ⟦ rose  S       (n ∷₁ []₁)           ⟧ᵥ ρ = suc (⟦ n ⟧ᵥ ρ)
  ⟦ rose  Fold    (f ∷₁ x ∷₁ n ∷₁ []₁) ⟧ᵥ ρ = fold (⟦ x ⟧ᵥ ρ) (⟦ f ⟧ᵥ ρ) (⟦ n ⟧ᵥ ρ)

  eval : ∀ {σ} -> Term⁽⁾ σ -> ⟦ σ ⟧
  eval t = ⟦ t ⟧ᵥ ∅



  A : ∀ {σ τ} -> Term⁺ ((σ ⇒ τ) ⇒ σ ⇒ τ)
  A = ƛ ƛ var (vs vz) · var vz

  test : ∀ {σ τ} -> eval (A {σ} {τ}) ≡ _$_
  test = refl
