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

  Frm-λ↓ = {!!}
  Frm-ap↓ = {!!}
