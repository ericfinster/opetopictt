{-# OPTIONS --without-K --rewriting #-}

open import Base
open import OpetopicType
open import OpetopicTypeOver
open import Sigma

module CellDep where

  postulate

    Cell↓-in : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set} {n : ℕ}
      → {γf : Frm Γ n} {γσ : Tree Γ γf} {γτ : Cell Γ γf} {γθ : Cell Γ (γf ∣ γσ ▸ γτ)}
      → {af : Frm↓ Γ A γf} {aσ : Tree↓ Γ A af γσ} {aτ : Cell↓ Γ A af γτ} {aθ : Cell↓ Γ A (af ∥ aσ ▸ aτ) γθ}
      → {bf : Frm↓ (Σ Γ A) B (Frm-pr γf af)}  (bσ : Tree↓ (Σ Γ A) B bf (Tree-pr γσ aσ))

      → (bτ₀ : Cell↓ (Σ Γ A) B bf (Cell-pr γτ aτ))
      → (bθ₀ : Cell↓ (Σ Γ A) B (bf ∥ bσ ▸ bτ₀) (Cell-pr γθ aθ))
      
      → (bτ₁ : Cell↓ (Σ Γ A) B bf (Cell-pr γτ aτ))
      → (bθ₁ : Cell↓ (Σ Γ A) B (bf ∥ bσ ▸ bτ₁) (Cell-pr γθ aθ))

      → (p : Cell (Cell↓ (Σ Γ A) B bf (Cell-pr γτ aτ)) (● ∣ ob [ bτ₀ ]↑ ▸ [ bτ₁ ]↑))
      
      -- MISSING! A witness that bθ₀ ∘ p = bθ₁. 

      --  And now we have to say that the triangle commutes.
      --  But for the moment, this is still problematic: we have
      --  a *fiberwise* equality between our two candidates, but how
      --  do we then make a commutative diagram?

      → Cell↓ (Cell↓ (Σ Γ A) B bf (Cell-pr γτ aτ))
              (λ bτ → Cell↓ (Σ Γ A) B (bf ∥ bσ ▸ bτ) (Cell-pr γθ aθ))
              (■ ∥ ob↓ ⟦ _ ∣ bθ₀ ⟧↑ ▸ ⟦ _ ∣ bθ₁ ⟧↑) p

