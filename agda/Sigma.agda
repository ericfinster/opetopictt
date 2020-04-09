{-# OPTIONS --without-K --rewriting #-}

open import Base
open import Opetopes
open import OpetopicType
open import OpetopicTypeOver

module Sigma where

  -- Rules for non-dependent Σ
  -- (i.e. context extension) using rewrites
    
  Frm-fst : {A : Set} {B : A → Set}
    → {n : ℕ} {o : 𝕆 n}
    → (f : Frm (Σ A B) o)
    → Frm A o

  Frm-snd : {A : Set} {B : A → Set}
    → {n : ℕ} {o : 𝕆 n}
    → (f : Frm (Σ A B) o)
    → Frm↓ A B (Frm-fst f)

  Tree-fst : {A : Set} {B : A → Set}
    → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → {f : Frm (Σ A B) o}
    → Tree (Σ A B) f t → Tree A (Frm-fst f) t

  Tree-snd : {A : Set} {B : A → Set}
    → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → {f : Frm (Σ A B) o}
    → (σ : Tree (Σ A B) f t)
    → Tree↓ A B (Frm-snd f) (Tree-fst σ)
    
  postulate

    Cell-Σ : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n}
      → {f : Frm (Σ A B) o}
      → Cell (Σ A B) f ↦ Σ (Cell A (Frm-fst f)) (Cell↓ A B (Frm-snd f))
    {-# REWRITE Cell-Σ #-}

    Tree-fst-typ : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm (Σ A B) o} (σ : Tree (Σ A B) f t)
      → (p : Pos t)
      → Typ (Tree-fst σ) p ↦ Frm-fst (Typ σ p)
    {-# REWRITE Tree-fst-typ #-}

    Tree-snd-typ : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm (Σ A B) o} (σ : Tree (Σ A B) f t)
      → (p : Pos t)
      → Typ↓ (Tree-snd σ) p ↦ Frm-snd (Typ σ p)
    {-# REWRITE Tree-snd-typ #-}
      
    Tree-fst-inh : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm (Σ A B) o} (σ : Tree (Σ A B) f t)
      → (p : Pos t)
      → Inh (Tree-fst σ) p ↦ fst (Inh σ p)
    {-# REWRITE Tree-fst-inh #-}

    Tree-snd-inh : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm (Σ A B) o} (σ : Tree (Σ A B) f t)
      → (p : Pos t)
      → Inh↓ (Tree-snd σ) p ↦ snd (Inh σ p)
    {-# REWRITE Tree-snd-inh #-}

    Tree-fst-η : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n} 
      → {f : Frm (Σ A B) o} (τ : Cell (Σ A B) f)
      → Tree-fst (η f τ) ↦ η (Frm-fst f) (fst τ)
    {-# REWRITE Tree-fst-η #-}

    Tree-snd-η : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n} 
      → {f : Frm (Σ A B) o} (τ : Cell (Σ A B) f)
      → Tree-snd (η f τ) ↦ η↓ (Frm-snd f) (snd τ)
    {-# REWRITE Tree-snd-η #-}
    
    Tree-fst-μ : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
      → {f : Frm (Σ A B) o} (σ : Tree (Σ A B) f t)
      → (δ : (p : Pos t) → Tree (Σ A B) (Typ σ p) (δₒ p))
      → Tree-fst (μ σ δ) ↦ μ (Tree-fst σ) (λ p → Tree-fst (δ p))
    {-# REWRITE Tree-fst-μ #-}

    Tree-snd-μ : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
      → {f : Frm (Σ A B) o} (σ : Tree (Σ A B) f t)
      → (δ : (p : Pos t) → Tree (Σ A B) (Typ σ p) (δₒ p))
      → Tree-snd (μ σ δ) ↦ μ↓ (Tree-snd σ) (λ p → Tree-snd (δ p))
    {-# REWRITE Tree-snd-μ #-}

  Frm-fst (□ a₀ ▹ a₁) = □ fst a₀ ▹ fst a₁
  Frm-fst (f ∥ σ ▹ τ) = Frm-fst f ∥ Tree-fst σ ▹ fst τ
  
  Frm-snd (□ a₀ ▹ a₁) = ■ snd a₀ ▸ snd a₁
  Frm-snd (f ∥ σ ▹ τ) = Frm-snd f ∥ Tree-snd σ ▸ snd τ

  Tree-fst (nil a) = nil (fst a)
  Tree-fst (cns ρ σ) = cns (fst ρ) (Tree-fst σ)
  Tree-fst (lf f τ) = lf (Frm-fst f) (fst τ)
  Tree-fst (nd σ τ θ δ ε) = nd (Tree-fst σ) (fst τ) (fst θ)
    (λ p → Tree-fst (δ p)) (λ p → Tree-fst (ε p))
  
  Tree-snd (nil a) = nil↓ (snd a)
  Tree-snd (cns ρ σ) = cns↓ (snd ρ) (Tree-snd σ)
  Tree-snd (lf f τ) = lf↓ (Frm-snd f) (snd τ)
  Tree-snd (nd σ τ θ δ ε) = nd↓ (Tree-snd σ) (snd τ) (snd θ)
    (λ p → Tree-snd (δ p)) (λ p → Tree-snd (ε p))
