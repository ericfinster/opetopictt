{-# OPTIONS --without-K --rewriting #-}

open import Base
open import OpetopicType
open import OpetopicTypeOver
open import Sigma

module PiDep where

  -- Dependent Π 
  Π↑ : {Γ : Set} (A : Γ → Set) (B : Σ Γ A → Set) → Γ → Set
  Π↑ {Γ} A B γ = Π (A γ) (λ a → B (γ , a))

  Frm-λ↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
    → {n : ℕ} {f : Frm Γ n}
    → (λf : (a↓ : Frm↓ Γ A f) → Frm↓ (Σ Γ A) B (Frm-pr f a↓))
    → Frm↓ Γ (Π↑ A B) f

  Frm-ap↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
    → {n : ℕ} {f : Frm Γ n}
    → (π↓ : Frm↓ Γ (Π↑ A B) f)
    → (a↓ : Frm↓ Γ A f)
    → Frm↓ (Σ Γ A) B (Frm-pr f a↓)

  postulate

    Cell-λ↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {γ : Cell Γ f}
      → (λf : (a↓ : Frm↓ Γ A f) → Frm↓ (Σ Γ A) B (Frm-pr f a↓))
      → (λb : (a↓ : Frm↓ Γ A f) (a : Cell↓ Γ A a↓ γ) → Cell↓ (Σ Γ A) B (λf a↓) (Cell-pr γ a))
      → Cell↓ Γ (Π↑ A B) (Frm-λ↓ λf) γ

    -- Have to redo the above with convention that the frame
    -- is given by subscript₀ ...
    Cell-ap↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {γ₀ : Frm Γ n} {γ : Cell Γ γ₀}
      → {σ₀ : Frm↓ Γ (Π↑ A B) γ₀} (σ : Cell↓ Γ (Π↑ A B) σ₀ γ)
      → {a₀ : Frm↓ Γ A γ₀} (a : Cell↓ Γ A a₀ γ)
      → Cell↓ (Σ Γ A) B (Frm-ap↓ σ₀ a₀) (Cell-pr γ a)

  Frm-λ↓ = {!!}
  Frm-ap↓ = {!!}
