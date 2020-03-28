{-# OPTIONS --without-K --rewriting #-}

open import Base
open import OpetopicType
open import OpetopicTypeOver
open import Sigma

module PiDep where

  -- Dependent Π
  
  Π↑ : {Γ : Set} (A : Γ → Set) (B : Σ Γ A → Set) → Γ → Set
  Π↑ A B γ = Π (A γ) (λ a → B (γ , a))

  Frm-λ↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
    → {n : ℕ} {γ₀ : Frm Γ n}
    → (b₀ : (a₀ : Frm↓ Γ A γ₀) → Frm↓ (Σ Γ A) B (Frm-pr γ₀ a₀))
    → Frm↓ Γ (Π↑ A B) γ₀

  Frm-ap↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
    → {n : ℕ} {γ₀ : Frm Γ n}
    → (π₀ : Frm↓ Γ (Π↑ A B) γ₀)
    → (a₀ : Frm↓ Γ A γ₀)
    → Frm↓ (Σ Γ A) B (Frm-pr γ₀ a₀)

  Tree-λ↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
    → {n : ℕ} {γ₀ : Frm Γ n} {γ : Tree Γ γ₀}
    → (b₀ : (a₀ : Frm↓ Γ A γ₀) → Frm↓ (Σ Γ A) B (Frm-pr γ₀ a₀))
    → (b : (a₀ : Frm↓ Γ A γ₀) (a : Tree↓ Γ A a₀ γ) → Tree↓ (Σ Γ A) B (b₀ a₀) (Tree-pr γ a))
    → Tree↓ Γ (Π↑ A B) (Frm-λ↓ b₀) γ

  Tree-ap↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
    → {n : ℕ} {γ₀ : Frm Γ n} (γ : Tree Γ γ₀)
    → {π₀ : Frm↓ Γ (Π↑ A B) γ₀} (π : Tree↓ Γ (Π↑ A B) π₀ γ)
    → (a₀ : Frm↓ Γ A γ₀) (a : Tree↓ Γ A a₀ γ)
    → Tree↓ (Σ Γ A) B (Frm-ap↓ π₀ a₀) (Tree-pr γ a)
  
  postulate

    Cell-λ↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {γ₀ : Frm Γ n} {γ : Cell Γ γ₀}
      → (b₀ : (a₀ : Frm↓ Γ A γ₀) → Frm↓ (Σ Γ A) B (Frm-pr γ₀ a₀))
      → (b : (a₀ : Frm↓ Γ A γ₀) (a : Cell↓ Γ A a₀ γ) → Cell↓ (Σ Γ A) B (b₀ a₀) (Cell-pr γ a))
      → Cell↓ Γ (Π↑ A B) (Frm-λ↓ b₀) γ

    Cell-ap↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {γ₀ : Frm Γ n} {γ : Cell Γ γ₀}
      → {π₀ : Frm↓ Γ (Π↑ A B) γ₀} (π : Cell↓ Γ (Π↑ A B) π₀ γ)
      → {a₀ : Frm↓ Γ A γ₀} (a : Cell↓ Γ A a₀ γ)
      → Cell↓ (Σ Γ A) B (Frm-ap↓ π₀ a₀) (Cell-pr γ a) 

  Frm-λ↓ = {!!}
  Frm-ap↓ = {!!}

  Tree-λ↓ = {!!}
  Tree-ap↓ = {!!}
