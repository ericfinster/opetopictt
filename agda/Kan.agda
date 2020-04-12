{-# OPTIONS --without-K --rewriting #-}

open import Base
open import Opetopes
open import OpetopicType

module Kan where

  postulate

    comp : {A : Set} {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm A o} (σ : Tree A f t)
      → Cell A f

    fill : {A : Set} {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm A o} (σ : Tree A f t)
      → Cell A (f ∥ σ ▹ comp σ)

    comp-elim : {A : Set} {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm A o} (σ : Tree A f t)
      → (τ : Cell A f) (θ : Cell A (f ∥ σ ▹ τ))
      → Cell A (f ∥ η f (comp σ) ▹ τ)

    comp-coh : {A : Set} {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm A o} (σ : Tree A f t)
      → (τ : Cell A f) (θ : Cell A (f ∥ σ ▹ τ))
      → Cell A (f ∥ σ ▹ τ ∥ nd (η f (comp σ)) τ (comp-elim σ τ θ) (λ _ → σ) (λ p → η _ (fill σ)) ▹ θ)

