open import Function hiding (_∋_) renaming (const to ᵏ_)
open import Data.Empty
open import Data.Unit.Base
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Product renaming (uncurry to ᵛ; curry to ̂)

infix  4 _∋_ _⊢_
infixr 6 _⇒_ _⇒ᵗ_
infixr 7 _×ᵗ_
infixl 5 _▻_
infixr 7 ƛ_ η_
infixr 8 vs_
infixl 8 _·_

-- We could write `⟦ pair x y ⟧ = ᵏ′ _,_ ˢ ⟦ x ⟧ ˢ ⟦ y ⟧`.
-- ᵏ′ : ∀ {α β} {A : Set α} {B : A -> Set β} -> (∀ {x} -> B x) -> ∀ x -> B x
-- ᵏ′ y x = y

elimBool : ∀ {π} -> (P : Bool -> Set π) -> P true -> P false -> ∀ b -> P b
elimBool P x y true  = x
elimBool P x y false = y

elimℕ : ∀ {π} -> (P : ℕ -> Set π) -> (∀ n -> P n -> P (suc n)) -> P 0 -> ∀ n -> P n
elimℕ P f z  0      = z
elimℕ P f z (suc n) = f n (elimℕ P f z n)

mutual
  data U : Set where
    bot top bool nat : U
    σ π : ∀ A -> (⟦ A ⟧ᵘ -> U) -> U

  ⟦_⟧ᵘ : U -> Set
  ⟦ bot   ⟧ᵘ = ⊥
  ⟦ top   ⟧ᵘ = ⊤
  ⟦ bool  ⟧ᵘ = Bool
  ⟦ nat   ⟧ᵘ = ℕ
  ⟦ σ A B ⟧ᵘ = ∃ λ x -> ⟦ B x ⟧ᵘ
  ⟦ π A B ⟧ᵘ = ∀   x -> ⟦ B x ⟧ᵘ

_⇒_ : U -> U -> U
A ⇒ B = π A λ _ -> B

mutual
  data Con : Set where
    ε   : Con
    _▻_ : ∀ Γ -> IU Γ -> Con

  IU : Con -> Set
  IU Γ = ⟦ Γ ⟧ᶜ -> U

  ⟦_⟧ᶜ : Con -> Set
  ⟦ ε     ⟧ᶜ = ⊤
  ⟦ Γ ▻ A ⟧ᶜ = ∃ λ ρ -> ⟦ A ρ ⟧ᵘ

⟦_⟧ⁱᵘ : ∀ {Γ} -> IU Γ -> Set
⟦ A ⟧ⁱᵘ = ∀ ρ -> ⟦ A ρ ⟧ᵘ

data _∋_ : ∀ Γ -> IU Γ -> Set where
  vz  : ∀ {Γ A}   ->          Γ ▻ A ∋ A ∘ proj₁
  vs_ : ∀ {Γ A B} -> Γ ∋ A -> Γ ▻ B ∋ A ∘ proj₁

lookup : ∀ {Γ A} -> Γ ∋ A -> ⟦ A ⟧ⁱᵘ
lookup  vz    (ρ , x) = x
lookup (vs v) (ρ , x) = lookup v ρ

mutual
  data Type {Γ} : IU Γ -> Set where
    botᵗ  : Type (ᵏ bot)
    topᵗ  : Type (ᵏ top)
    boolᵗ : Type (ᵏ bool)    
    natᵗ  : Type (ᵏ nat)
    _×ᵗ_  : ∀ {A B} -> Type A -> Type B -> Type (σ ∘ A ˢ ̂ B)
    _⇒ᵗ_  : ∀ {A B} -> Type A -> Type B -> Type (π ∘ A ˢ ̂ B)
    recbᵗ : ∀ {A B} -> Type A -> Type B -> (b : Γ ⊢ ᵏ bool) -> Type (if_then_else_ ∘ ⟦ b ⟧ ˢ A ˢ B)

  data _⊢_ Γ : IU Γ -> Set where
    var   : ∀ {A} -> Γ ∋ A -> Γ ⊢ A
    any   : ∀ {A} -> Γ ⊢ ᵏ bot -> Γ ⊢ ᵏ A
    unit  : Γ ⊢ ᵏ top
    tr    : Γ ⊢ ᵏ bool
    fa    : Γ ⊢ ᵏ bool
    elimb : ∀ {P} -> Type (ᵛ P) -> Γ ⊢ flip P true -> Γ ⊢ flip P false -> ∀ b -> Γ ⊢ P ˢ ⟦ b ⟧
    ze    : Γ ⊢ ᵏ nat
    su    : Γ ⊢ ᵏ nat -> Γ ⊢ ᵏ nat
    elimn : ∀ {P}
          -> Type (ᵛ P)
          -> Γ ⊢ (λ ρ -> π nat λ n -> P ρ n ⇒ P ρ (suc n))
          -> Γ ⊢ flip P 0
          -> ∀ n
          -> Γ ⊢ P ˢ ⟦ n ⟧
    pair  : ∀ {A B} -> (x : Γ ⊢ A) -> Γ ⊢ B ˢ ⟦ x ⟧ -> Γ ⊢ σ ∘ A ˢ B
    fst   : ∀ {A B} ->      Γ ⊢ σ ∘ A ˢ B  -> Γ ⊢ A
    snd   : ∀ {A B} -> (p : Γ ⊢ σ ∘ A ˢ B) -> Γ ⊢ B ˢ ⟦ fst p ⟧
    ƛ_    : ∀ {A B} -> Γ ▻ A ⊢ ᵛ B -> Γ ⊢ π ∘ A ˢ B
    _·_   : ∀ {A B} -> Γ ⊢ π ∘ A ˢ B -> (x : Γ ⊢ A) -> Γ ⊢ B ˢ ⟦ x ⟧

  ⟦_⟧ᵗ : ∀ {Γ A} -> Type {Γ} A -> ⟦ Γ ⟧ᶜ -> Set
  ⟦_⟧ᵗ {A = A} _ = ⟦_⟧ᵘ ∘ A

  ⟦_⟧ : ∀ {Γ A} -> Γ ⊢ A -> ⟦ A ⟧ⁱᵘ
  ⟦ var x         ⟧ = lookup x
  ⟦ any f         ⟧ = ⊥-elim ∘ ⟦ f ⟧
  ⟦ unit          ⟧ = ᵏ tt
  ⟦ tr            ⟧ = ᵏ true
  ⟦ fa            ⟧ = ᵏ false
  ⟦ elimb P x y b ⟧ = elimBool ∘ ̂ ⟦ P ⟧ᵗ ˢ ⟦ x ⟧ ˢ ⟦ y ⟧ ˢ ⟦ b ⟧
  ⟦ ze            ⟧ = ᵏ 0
  ⟦ su n          ⟧ = suc ∘ ⟦ n ⟧
  ⟦ elimn P f x n ⟧ = elimℕ    ∘ ̂ ⟦ P ⟧ᵗ ˢ ⟦ f ⟧ ˢ ⟦ x ⟧ ˢ ⟦ n ⟧
  ⟦ pair x y      ⟧ = _,_ ∘ ⟦ x ⟧ ˢ ⟦ y ⟧
  ⟦ fst p         ⟧ = proj₁ ∘ ⟦ p ⟧
  ⟦ snd p         ⟧ = proj₂ ∘ ⟦ p ⟧
  ⟦ ƛ b           ⟧ = ̂ ⟦ b ⟧
  ⟦ f · x         ⟧ = ⟦ f ⟧ ˢ ⟦ x ⟧

Type⁺ : U -> Set
Type⁺ A = ∀ {Γ} -> Type {Γ} (ᵏ A)

Term⁺ : ∀ {A} -> Type⁺ A -> Set
Term⁺ {A} _ = ∀ {Γ} -> Γ ⊢ ᵏ A

η_ : ∀ {Γ A B} -> (∀ x -> Γ ▻ A ⊢ B ∘ proj₁ ˢ ⟦ x ⟧) -> Γ ⊢ π ∘ A ˢ B
η_ f = ƛ f (var vz)

trueᵗ : ∀ {Γ} -> (b : Γ ⊢ ᵏ bool) -> Type _
trueᵗ = recbᵗ topᵗ botᵗ

add : Term⁺ (natᵗ ⇒ᵗ natᵗ ⇒ᵗ natᵗ)
add = ƛ ƛ elimn natᵗ (ƛ η su) (var vz) (var (vs vz))

natEq : Term⁺ (natᵗ ⇒ᵗ natᵗ ⇒ᵗ boolᵗ)
natEq = η elimn (natᵗ ⇒ᵗ boolᵗ)
                (ƛ ƛ η elimn boolᵗ (ƛ ƛ var (vs vs vs vz) · var (vs vz)) fa)
                (η elimn boolᵗ (ƛ ƛ fa) tr)

refl : Term⁺ (natᵗ ⇒ᵗ trueᵗ (natEq · var vz · var vz))
refl = η elimn (trueᵗ (natEq · var vz · var vz)) (ƛ η id) unit
