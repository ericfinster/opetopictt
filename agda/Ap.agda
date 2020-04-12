{-# OPTIONS --without-K --rewriting #-}

open import Base
open import Opetopes
open import OpetopicType

module Ap where

  -- Primitive non-dependent ap

  Frm-ap : {A B : Set} (ϕ : A → B)
    → {n : ℕ} {o : 𝕆 n}
    → Frm A o → Frm B o

  Tree-ap : {A B : Set} (ϕ : A → B)
    → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → {f : Frm A o} (σ : Tree A f t)
    → Tree B (Frm-ap ϕ f) t

  postulate

    Cell-ap : {A B : Set} (ϕ : A → B)
      → {n : ℕ} {o : 𝕆 n}
      → {f : Frm A o} 
      → Cell A f → Cell B (Frm-ap ϕ f)

    Tree-ap-typ : {A B : Set} (ϕ : A → B)
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → (f : Frm A o) (σ : Tree A f t)
      → (p : Pos t)
      → Typ (Tree-ap ϕ σ) p ↦ Frm-ap ϕ (Typ σ p)
    {-# REWRITE Tree-ap-typ #-}

    Tree-ap-inh : {A B : Set} (ϕ : A → B)
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → (f : Frm A o) (σ : Tree A f t)
      → (p : Pos t)
      → Inh (Tree-ap ϕ σ) p ↦ Cell-ap ϕ (Inh σ p)
    {-# REWRITE Tree-ap-inh #-}

    Tree-ap-η : {A B : Set} (ϕ : A → B)
      → {n : ℕ} {o : 𝕆 n} 
      → (f : Frm A o) (τ : Cell A f)
      → Tree-ap ϕ (η f τ) ↦ η (Frm-ap ϕ f) (Cell-ap ϕ τ)
    {-# REWRITE Tree-ap-η #-}

    Tree-ap-μ : {A B : Set} (ϕ : A → B)
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
      → {f : Frm A o} (σ : Tree A f t)
      → (δ : (p : Pos t) → Tree A (Typ σ p) (δₒ p))
      → Tree-ap ϕ (μ σ δ) ↦ μ (Tree-ap ϕ σ) (λ p → Tree-ap ϕ (δ p))
    {-# REWRITE Tree-ap-μ #-}

  Frm-ap ϕ (□ a₀ ▹ a₁) = □ ϕ a₀ ▹ ϕ a₁
  Frm-ap ϕ (f ∥ σ ▹ τ) = Frm-ap ϕ f ∥ Tree-ap ϕ σ ▹ Cell-ap ϕ τ
  
  Tree-ap ϕ (nil a) = nil (ϕ a)
  Tree-ap ϕ (cns ρ σ) = cns (Cell-ap ϕ ρ) (Tree-ap ϕ σ)
  Tree-ap ϕ (lf f τ) = lf (Frm-ap ϕ f) (Cell-ap ϕ τ)
  Tree-ap ϕ (nd σ τ θ δ ε) = nd (Tree-ap ϕ σ) (Cell-ap ϕ τ) (Cell-ap ϕ θ)
    (λ p → Tree-ap ϕ (δ p)) (λ p → Tree-ap ϕ (ε p))
