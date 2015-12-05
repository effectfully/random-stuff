module System-F.Subst where

open import System-F.Prelude
open import System-F.Kits
open import System-F.Core

-- This is awful.
module _ where
  open TypeThing
  open TypeEnvironment

  ren-lookup-top : ∀ {Θ Ξ σ τ} {α : Θ ⊢ᵗ σ} Γ (ι : Θ ⊆ Ξ) (v : τ ∈ Θ ▻ σ ▻▻ Γ)
                 ->   renᵗ (keeps Γ ι) (lookupᵉ v (keepsᵉ Γ (topᵉ α)))
                    ≡ lookupᵉ (renᵛ (keeps Γ (keep ι)) v) (keepsᵉ Γ (topᵉ (renᵗ ι α)))
  ren-lookup-top  ε      ι  vz    = refl
  ren-lookup-top  ε      ι (vs v) = trans (cong (renᵗ ι) (lookupᵉ-idᵉ v))
                                          (sym (lookupᵉ-idᵉ (renᵛ ι v)))
  ren-lookup-top (Γ ▻ σ) ι  vz    = refl
  ren-lookup-top (Γ ▻ σ) ι (vs v) =
    trans (cong (renᵗ (keep (keeps Γ ι))) (lookupᵉ-renᵉ v top _))
          (trans (renᵗ-∘ˢ (keep (keeps Γ ι)) top _)
                 (trans (trans (trans (trans (cong (λ ι -> renᵗ (skip ι) _)
                                                   (∘ˢ-idˢ (keeps Γ ι)))
                                             (cong (λ ι -> renᵗ (skip ι) _)
                                                   (sym (idˢ-∘ˢ (keeps Γ ι)))))
                                      (sym (renᵗ-∘ˢ top (keeps Γ ι) _)))
                               (cong shiftᵗ (ren-lookup-top Γ ι v)))
                        (sym (lookupᵉ-renᵉ (renᵛ (keeps Γ (keep ι)) v) top _))))

-- renᵗ  ι       (subᵗ        (topᵉ α)  β) ≡ subᵗ        (topᵉ (renᵗ ι α))  (renᵗ       (keep ι) β)
-- renᵗ (keep ι) (subᵗ (keepᵉ (topᵉ α)) β) ≡ subᵗ (keepᵉ (topᵉ (renᵗ ι α))) (renᵗ (keep (keep ι) β))
  ren-sub-top : ∀ {Θ Ξ σ τ} {α : Θ ⊢ᵗ σ} Γ (ι : Θ ⊆ Ξ) (β : Θ ▻ σ ▻▻ Γ ⊢ᵗ τ)
              ->   renᵗ (keeps Γ ι) (subᵗ (keepsᵉ Γ (topᵉ α)) β)
                 ≡ subᵗ (keepsᵉ Γ (topᵉ (renᵗ ι α))) (renᵗ (keeps Γ (keep ι)) β)
  ren-sub-top Γ ι (Var v)  = ren-lookup-top Γ ι v
  ren-sub-top Γ ι (f ·ᵗ β) = cong₂ _·ᵗ_ (ren-sub-top Γ ι f) (ren-sub-top Γ ι β)
  ren-sub-top Γ ι (β ⇒ γ)  = cong₂ _⇒_  (ren-sub-top Γ ι β) (ren-sub-top Γ ι γ)
  ren-sub-top Γ ι (π σ β)  = cong (π σ) (ren-sub-top (Γ ▻ σ) ι β)

  ren-top-sub : ∀ {Θ Ξ σ} {α : Θ ⊢ᵗ σ} (ι : Θ ⊆ Ξ) (β : Type (Θ ▻ σ))
              -> renᵗ ι (β [ α ]ᵗ) ≡ renᵗ (keep ι) β [ renᵗ ι α ]ᵗ
  ren-top-sub = ren-sub-top ε

  rename : ∀ {Θ Ξ α} {Γ : Conᵗ Θ} -> (ι : Θ ⊆ Ξ) -> Γ ⊢ α -> renᶜ ι Γ ⊢ renᵗ ι α
  rename ι (var v)            = var (renameᵛ ι v)
  rename ι (Λ b)              = Λ (coerceCon (trans (renᶜ-∘ˢ (keep ι) top _)
                                                    (trans (cong (λ ι -> renᶜ (skip ι) _)
                                                                 (trans (∘ˢ-idˢ ι) (sym (idˢ-∘ˢ ι))))
                                                           (sym (renᶜ-∘ˢ top ι _))))
                                             (rename (keep ι) b))
  rename ι (_[_] {β = β} f α) rewrite ren-top-sub {α = α} ι β
                              = rename ι f [ renᵗ ι α ]
  rename ι (ƛ b)              = ƛ (rename ι b)
  rename ι (f · x)            = rename ι f · rename ι x

TermNestedEnvs : NestedEnvironments TermEnv TypeEnv
TermNestedEnvs = record
  { renⁿᶠ = rename
  }

open TermEnvironment
open NestedEnvironments TermNestedEnvs

sub : ∀ {Θ Γ Δ} {σ : Type Θ} -> Δ ⊢ᵉ Γ -> Γ ⊢ σ -> Δ ⊢ σ
sub ρ (var v)   = lookupᵉ v ρ
sub ρ (Λ b)     = Λ (sub (shiftᵉ-⊆ ρ) b)
sub ρ (f [ α ]) = sub ρ f [ α ]
sub ρ (ƛ b)     = ƛ sub (keepᵉ ρ) b
sub ρ (f · x)   = sub ρ f · sub ρ x
