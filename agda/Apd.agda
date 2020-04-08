{-# OPTIONS --without-K --rewriting #-}

open import Base
open import OpetopicType
open import OpetopicTypeOver

module Apd where

  -- Primitive dependent application

  Frm-apd : {A : Set} {B : A → Set}
    → (b : (a : A) → B a)
    → {n : ℕ} (f : Frm A n)
    → Frm↓ A B f

  Tree-apd : {A : Set} {B : A → Set}
    → (b : (a : A) → B a)
    → {n : ℕ} {f : Frm A n}
    → (σ : Tree A f) → Tree↓ A B (Frm-apd b f) σ

  postulate

    Cell-apd : {A : Set} {B : A → Set}
      → (b : (a : A) → B a)
      → {n : ℕ} {f : Frm A n}
      → (a : Cell A f) → Cell↓ A B (Frm-apd b f) a

    Typ-apd : {A : Set} {B : A → Set}
      → (b : (a : A) → B a)
      → {n : ℕ} {f : Frm A n}
      → (σ : Tree A f) (p : Pos σ)
      → Frm-apd b (Typ σ p) ↦ Typ↓ (Tree-apd b σ) p
    {-# REWRITE Typ-apd #-}

    Inh-apd : {A : Set} {B : A → Set}
      → (b : (a : A) → B a)
      → {n : ℕ} {f : Frm A n}
      → (σ : Tree A f) (p : Pos σ)
      → Cell-apd b (Inh σ p) ↦ Inh↓ (Tree-apd b σ) p
    {-# REWRITE Inh-apd #-}
      
    Tree-apd-η : {A : Set} {B : A → Set}
      → (b : (a : A) → B a)
      → {n : ℕ} {f : Frm A n} (τ : Cell A f)
      → Tree-apd b (η f τ) ↦ η↓ (Frm-apd b f) (Cell-apd b τ)
    {-# REWRITE Tree-apd-η #-}

    Tree-apd-μ : {A : Set} {B : A → Set}
      → (b : (a : A) → B a)
      → {n : ℕ} {f : Frm A n} (σ : Tree A f)
      → (δ : (p : Pos σ) → Tree A (Typ σ p))
      → Tree-apd b (μ σ δ) ↦ μ↓ (Tree-apd b σ) (λ p → Tree-apd b (δ p))
    {-# REWRITE Tree-apd-μ #-}

  Frm-apd b ● = ■
  Frm-apd b (f ∣ σ ▸ τ) =
    Frm-apd b f ∥ Tree-apd b σ ▸ Cell-apd b τ
  
  Tree-apd b (ob τ) = ob↓ (Cell-apd b τ)
  Tree-apd b (lf f τ) = lf↓ (Frm-apd b f) (Cell-apd b τ)
  Tree-apd b (nd f σ τ θ δ ε) =
    nd↓ (Tree-apd b σ) (Cell-apd b τ) (Cell-apd b θ)
      (λ p → Tree-apd b (δ p))
      (λ p → Tree-apd b (ε p))

