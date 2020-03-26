{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Base
open import OpetopicType
open import OpetopicTypeOver

module Universe where

  𝕌 = Set
    
  postulate

    -- So it looks like the basic setup for the universe will just be
    -- an explicit intro/elim pair stating that cells in the universe
    -- are equivalent to a certain type (namely, higher opetopic
    -- equivalences).  And then additionally, rules for introducing
    -- elements into the universal fibration.

    Cell-𝕌-in : {n : ℕ} {f : Frm 𝕌 n}
      → (σ : Tree 𝕌 f) (τ : Cell 𝕌 f)
      → (E : (f↓ : Frm↓ 𝕌 (λ X → X) f) → Tree↓ 𝕌 (λ X → X) f↓ σ → Cell↓ 𝕌 (λ X → X) f↓ τ → Set)
      → Cell 𝕌 (f ∣ σ ▸ τ)

    Cell-𝕌↓-in : {n : ℕ} {f : Frm 𝕌 n}
      → (σ : Tree 𝕌 f) (τ : Cell 𝕌 f)
      → (E : (f↓ : Frm↓ 𝕌 (λ X → X) f) → Tree↓ 𝕌 (λ X → X) f↓ σ → Cell↓ 𝕌 (λ X → X) f↓ τ → Set)
      → (f↓ : Frm↓ 𝕌 (λ X → X) f) (σ↓ : Tree↓ 𝕌 (λ X → X) f↓ σ) (τ↓ : Cell↓ 𝕌 (λ X → X) f↓ τ)
      → (e : E f↓ σ↓ τ↓)
      → Cell↓ 𝕌 (λ X → X) (f↓ ∥ σ↓ ▸ τ↓) (Cell-𝕌-in σ τ E)

    Cell-𝕌-out : {n : ℕ} {f : Frm 𝕌 n}
      → (σ : Tree 𝕌 f) (τ : Cell 𝕌 f)
      → (θ : Cell 𝕌 (f ∣ σ ▸ τ))
      → (f↓ : Frm↓ 𝕌 (λ X → X) f)
      → Tree↓ 𝕌 (λ X → X) f↓ σ → Cell↓ 𝕌 (λ X → X) f↓ τ → Set

    Cell-𝕌↓-out : {n : ℕ} {f : Frm 𝕌 n}
      → (σ : Tree 𝕌 f) (τ : Cell 𝕌 f)
      → (θ : Cell 𝕌 (f ∣ σ ▸ τ))
      → (f↓ : Frm↓ 𝕌 (λ X → X) f)
      → (σ↓ : Tree↓ 𝕌 (λ X → X) f↓ σ) (τ↓ : Cell↓ 𝕌 (λ X → X) f↓ τ)
      → (e : Cell↓ 𝕌 (λ X → X) (f↓ ∥ σ↓ ▸ τ↓) θ)
      → Cell-𝕌-out σ τ θ f↓ σ↓ τ↓

  -- Okay, okay.  This looks pretty good.

  -- And oddly enough, it seems that in contrast to the other type
  -- constructors, we *could* implement the rules for the universe as
  -- rewrites, since they only operate on the postulated cell types.

