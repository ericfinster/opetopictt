{-# OPTIONS --without-K --rewriting #-}

open import Base
open import Opetopes
open import OpetopicType
open import OpetopicTypeOver
open import Cell

module CellOverCell where

  -- Cell↓ in the fibration of fillers

  -- This is just the lowest dimensional case.  I believe
  -- it should have a generalization to all dimensions, but
  -- this is already a good start!

  postulate

    Cell↓-Cell : {A : Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm A o} {σ : Tree A f t}
      → (τ₀ : Cell A f) (θ₀ : Cell A (f ∥ σ ▹ τ₀))
      → (τ₁ : Cell A f) (θ₁ : Cell A (f ∥ σ ▹ τ₁))
      → (ϕ : Cell A (f ∥ η f τ₀ ▹ τ₁))
      → Cell↓ (Cell A f) (λ τ → Cell A (f ∥ σ ▹ τ)) {f = □ τ₀ ▹ τ₁} (■ θ₀ ▸ θ₁) ϕ ↦
        Cell A (f ∥ σ ▹ τ₁ ∥ nd (η f τ₀) τ₁ ϕ (λ _ → σ) (λ p → η (f ∥ σ ▹ τ₀) θ₀) ▹ θ₁)

