{-# OPTIONS --without-K --rewriting --allow-unsolved-meta #-}

open import Base
open import Opetopes
open import OpetopicType
open import OpetopicTypeOver

module Sigma where

  -- Rules for non-dependent Σ
  -- (i.e. context extension) using rewrites

  Frm-pr : {A : Set} {B : A → Set}
    → {n : ℕ} {o : 𝕆 n}
    → (f : Frm A o)
    → (f↓ : Frm↓ A B f)
    → Frm (Σ A B) o
    
  Frm-fst : {A : Set} {B : A → Set}
    → {n : ℕ} {o : 𝕆 n}
    → (f : Frm (Σ A B) o)
    → Frm A o

  Frm-snd : {A : Set} {B : A → Set}
    → {n : ℕ} {o : 𝕆 n}
    → (f : Frm (Σ A B) o)
    → Frm↓ A B (Frm-fst f)

  Tree-pr : {A : Set} {B : A → Set}
    → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → {f : Frm A o} {f↓ : Frm↓ A B f}
    → (σ : Tree A f t) (σ↓ : Tree↓ A B f↓ σ) 
    → Tree (Σ A B) (Frm-pr f f↓) t

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

    Tree-pr-typ : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm A o} (σ : Tree A f t)
      → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ)
      → (p : Pos t)
      → Typ (Tree-pr σ σ↓) p ↦ Frm-pr (Typ σ p) (Typ↓ σ↓ p)
    {-# REWRITE Tree-pr-typ #-}

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

    Frm-fst-β : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n}
      → (f : Frm A o)
      → (f↓ : Frm↓ A B f)
      → Frm-fst (Frm-pr f f↓) ↦ f
    {-# REWRITE Frm-fst-β #-}

    Frm-snd-β : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n}
      → (f : Frm A o)
      → (f↓ : Frm↓ A B f)
      → Frm-snd (Frm-pr f f↓) ↦ f↓
    {-# REWRITE Frm-snd-β #-}

    Frm-pr-β : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n}
      → (f : Frm (Σ A B) o)
      → Frm-pr (Frm-fst f) (Frm-snd f) ↦ f
    {-# REWRITE Frm-pr-β #-}

    Cell-Σ-Inh : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm A o} (σ : Tree A f t)
      → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ)
      → (p : Pos t)
      → Inh (Tree-pr σ σ↓) p ↦ Inh σ p , Inh↓ σ↓ p
    {-# REWRITE Cell-Σ-Inh #-}

    Tree-fst-β : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm A o} (σ : Tree A f t)
      → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ)
      → Tree-fst (Tree-pr σ σ↓) ↦ σ
    {-# REWRITE Tree-fst-β #-}

    Tree-snd-β : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm A o} (σ : Tree A f t)
      → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ)
      → Tree-snd (Tree-pr σ σ↓) ↦ σ↓
    {-# REWRITE Tree-snd-β #-}

    Tree-pr-β : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm (Σ A B) o} (σ : Tree (Σ A B) f t)
      → Tree-pr (Tree-fst σ) (Tree-snd σ) ↦ σ
    {-# REWRITE Tree-pr-β #-}

    Tree-pr-η : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n}
      → {f : Frm A o} (τ : Cell A f)
      → {f↓ : Frm↓ A B f} (τ↓ : Cell↓ A B f↓ τ)
      → Tree-pr (η f τ) (η↓ f↓ τ↓) ↦ η (Frm-pr f f↓) (τ , τ↓)
    {-# REWRITE Tree-pr-η #-}

    Tree-pr-μ : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
      → {f : Frm A o} {σ : Tree A f t}
      → {δ : (p : Pos t) → Tree A (Typ σ p) (δₒ p)}
      → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ)
      → (δ↓ : (p : Pos t) → Tree↓ A B (Typ↓ σ↓ p) (δ p))
      → Tree-pr (μ σ δ) (μ↓ σ↓ δ↓) ↦ μ (Tree-pr σ σ↓) λ p → Tree-pr {f = Typ σ p} {f↓ = Typ↓ σ↓ p} (δ p) (δ↓ p)
    {-# REWRITE Tree-pr-μ #-}

  Frm-pr (□ a₀ ▹ a₁) (■ b₀ ▸ b₁) = □ (a₀ , b₀) ▹ (a₁ , b₁)
  Frm-pr (f ∥ σ ▹ τ) (f↓ ∥ σ↓ ▸ τ↓) = Frm-pr f f↓ ∥ Tree-pr σ σ↓ ▹ (τ , τ↓)

  Frm-fst (□ a₀ ▹ a₁) = □ fst a₀ ▹ fst a₁
  Frm-fst (f ∥ σ ▹ τ) = Frm-fst f ∥ Tree-fst σ ▹ fst τ
  
  Frm-snd (□ a₀ ▹ a₁) = ■ snd a₀ ▸ snd a₁
  Frm-snd (f ∥ σ ▹ τ) = Frm-snd f ∥ Tree-snd σ ▸ snd τ

  Tree-pr (nil a) (nil↓ b) = nil (a , b)
  Tree-pr (cns ρ σ) (cns↓ ρ↓ σ↓) = cns (ρ , ρ↓) (Tree-pr σ σ↓) 
  Tree-pr (lf f τ) (lf↓ f↓ τ↓) = lf (Frm-pr f f↓) (τ , τ↓)
  Tree-pr (nd σ τ θ δ ε) (nd↓ σ↓ τ↓ θ↓ δ↓ ε↓) =
    let ϕ p = Tree-pr (δ p) (δ↓ p)
        ψ p = Tree-pr (ε p) (ε↓ p)
    in nd (Tree-pr σ σ↓) (τ , τ↓) (θ , θ↓) ϕ ψ

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
    
