{-# OPTIONS --without-K --rewriting #-}

open import Base
open import Opetopes
open import OpetopicType
open import OpetopicTypeOver

module Apd where

  -- Primitive dependent application

  Frm-apd : {A : Set} {B : A → Set}
    → (b : (a : A) → B a)
    → {n : ℕ} {o : 𝕆 n}
    → (f : Frm A o) → Frm↓ A B f

  Tree-apd : {A : Set} {B : A → Set}
    → (b : (a : A) → B a)
    → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → {f : Frm A o} (σ : Tree A f t)
    → Tree↓ A B (Frm-apd b f) σ

  postulate

    Cell-apd : {A : Set} {B : A → Set}
      → (b : (a : A) → B a)
      → {n : ℕ} {o : 𝕆 n}
      → {f : Frm A o} (a : Cell A f)
      → Cell↓ A B (Frm-apd b f) a

    Typ-apd : {A : Set} {B : A → Set}
      → (b : (a : A) → B a)
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm A o} (σ : Tree A f t)
      → (p : Pos t)
      → Frm-apd b (Typ σ p) ↦ Typ↓ (Tree-apd b σ) p
    {-# REWRITE Typ-apd #-}

    Inh-apd : {A : Set} {B : A → Set}
      → (b : (a : A) → B a)
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm A o} (σ : Tree A f t)
      → (p : Pos t)
      → Cell-apd b (Inh σ p) ↦ Inh↓ (Tree-apd b σ) p
    {-# REWRITE Inh-apd #-}
      
    Tree-apd-η : {A : Set} {B : A → Set}
      → (b : (a : A) → B a)
      → {n : ℕ} {o : 𝕆 n}
      → {f : Frm A o} (τ : Cell A f)
      → Tree-apd b (η f τ) ↦ η↓ (Frm-apd b f) (Cell-apd b τ)
    {-# REWRITE Tree-apd-η #-}

    Tree-apd-μ : {A : Set} {B : A → Set}
      → (b : (a : A) → B a)
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
      → {f : Frm A o} (σ : Tree A f t)
      → (δ : (p : Pos t) → Tree A (Typ σ p) (δₒ p))
      → Tree-apd b (μ σ δ) ↦ μ↓ (Tree-apd b σ) (λ p → Tree-apd b (δ p))
    {-# REWRITE Tree-apd-μ #-}

  Frm-apd b (□ a₀ ▹ a₁) = ■ b a₀ ▸ b a₁
  Frm-apd b (f ∥ σ ▹ τ) = 
    Frm-apd b f ∥ Tree-apd b σ ▸ Cell-apd b τ

  Tree-apd b (nil a) = nil↓ (b a)
  Tree-apd b (cns ρ σ) = cns↓ (Cell-apd b ρ) (Tree-apd b σ)
  Tree-apd b (lf f τ) = lf↓ (Frm-apd b f) (Cell-apd b τ)
  Tree-apd b (nd σ τ θ δ ε) =
    nd↓ (Tree-apd b σ) (Cell-apd b τ) (Cell-apd b θ)
      (λ p → Tree-apd b (δ p))
      (λ p → Tree-apd b (ε p))

