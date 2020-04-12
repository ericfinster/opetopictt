{-# OPTIONS --without-K --rewriting #-}

open import Base
open import Opetopes
open import OpetopicType
open import OpetopicTypeOver
open import Sigma

module SigmaDep where

  Σ↑ : {Γ : Set} (A : Γ → Set) (B : Σ Γ A → Set) → Γ → Set
  Σ↑ A B γ = Σ (A γ) (λ a → B (γ , a))

  Frm-fst↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
    → {n : ℕ} {o : 𝕆 n} {f : Frm Γ o}
    → Frm↓ Γ (Σ↑ A B) f
    → Frm↓ Γ A f

  Frm-snd↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
    → {n : ℕ} {o : 𝕆 n} {f : Frm Γ o}
    → (f↓ : Frm↓ Γ (Σ↑ A B) f)
    → Frm↓ (Σ Γ A) B (Frm-pr f (Frm-fst↓ f↓))

  Tree-fst↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
    → {n : ℕ} {o : 𝕆 n} {f : Frm Γ o} {t : 𝕋 o} {σ : Tree Γ f t}
    → {f↓ : Frm↓ Γ (Σ↑ A B) f}
    → Tree↓ Γ (Σ↑ A B) f↓ σ
    → Tree↓ Γ A (Frm-fst↓ f↓) σ

  Tree-snd↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
    → {n : ℕ} {o : 𝕆 n} {f : Frm Γ o} {t : 𝕋 o} {σ : Tree Γ f t}
    → {f↓ : Frm↓ Γ (Σ↑ A B) f}
    → (σ↓ : Tree↓ Γ (Σ↑ A B) f↓ σ)
    → Tree↓ (Σ Γ A) B (Frm-snd↓ f↓) (Tree-pr σ (Tree-fst↓ σ↓))
      
  postulate    
  
    Cell-pr↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {o : 𝕆 n} {f : Frm Γ o} {τ : Cell Γ f}
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → (τ↓ : Cell↓ Γ A (Frm-fst↓ f↓) τ)
      → (τ↓₁ : Cell↓ (Σ Γ A) B (Frm-snd↓ f↓) (τ , τ↓))
      → Cell↓ Γ (Σ↑ A B) f↓ τ

    Cell-fst↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {o : 𝕆 n} {f : Frm Γ o} {τ : Cell Γ f}
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → Cell↓ Γ (Σ↑ A B) f↓ τ
      → Cell↓ Γ A (Frm-fst↓ f↓) τ

    Cell-snd↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {o : 𝕆 n} {f : Frm Γ o} {τ : Cell Γ f}
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → (σ↓ : Cell↓ Γ (Σ↑ A B) f↓ τ)
      → Cell↓ (Σ Γ A) B (Frm-snd↓ f↓) (τ , (Cell-fst↓ σ↓))

    -- Cells equations
    Cell-fst-β↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {o : 𝕆 n} {f : Frm Γ o} {τ : Cell Γ f}
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → (τ↓ : Cell↓ Γ A (Frm-fst↓ f↓) τ)
      → (τ↓₁ : Cell↓ (Σ Γ A) B (Frm-snd↓ f↓) (τ , τ↓))
      → Cell-fst↓ (Cell-pr↓ τ↓ τ↓₁) ↦ τ↓
    {-# REWRITE Cell-fst-β↓ #-}

    Cell-snd-β↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {o : 𝕆 n} {f : Frm Γ o} {τ : Cell Γ f}
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → (τ↓ : Cell↓ Γ A (Frm-fst↓ f↓) τ)
      → (τ↓₁ : Cell↓ (Σ Γ A) B (Frm-snd↓ f↓) (τ , τ↓))
      → Cell-snd↓ (Cell-pr↓ τ↓ τ↓₁) ↦ τ↓₁
    {-# REWRITE Cell-snd-β↓ #-}

    Cell-pr-β↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {o : 𝕆 n} {f : Frm Γ o} {τ : Cell Γ f}
      → (f↓ : Frm↓ Γ (Σ↑ A B) f )
      → (τ↓ : Cell↓ Γ (Σ↑ A B) f↓ τ)
      → Cell-pr↓ (Cell-fst↓ τ↓) (Cell-snd↓ τ↓) ↦ τ↓
    {-# REWRITE Cell-pr-β↓ #-}

    Typ-fst↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {o : 𝕆 n} {f : Frm Γ o} {t : 𝕋 o} {σ : Tree Γ f t}
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → (σ↓ : Tree↓ Γ (Σ↑ A B) f↓ σ)
      → (p : Pos t)
      → Typ↓ (Tree-fst↓ σ↓) p ↦ Frm-fst↓ (Typ↓ σ↓ p) 
    {-# REWRITE Typ-fst↓ #-}

    Inh-fst↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {o : 𝕆 n} {f : Frm Γ o} {t : 𝕋 o} {σ : Tree Γ f t}
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → (σ↓ : Tree↓ Γ (Σ↑ A B) f↓ σ)
      → (p : Pos t)
      → Inh↓ (Tree-fst↓ σ↓) p ↦ Cell-fst↓ (Inh↓ σ↓ p) 
    {-# REWRITE Inh-fst↓ #-}

    Typ-snd↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {o : 𝕆 n} {f : Frm Γ o} {t : 𝕋 o} {σ : Tree Γ f t}
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → (σ↓ : Tree↓ Γ (Σ↑ A B) f↓ σ) (p : Pos t)
      → Typ↓ (Tree-snd↓ σ↓) p ↦ Frm-snd↓ (Typ↓ σ↓ p) 
    {-# REWRITE Typ-snd↓ #-}

    Inh-snd↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {o : 𝕆 n} {f : Frm Γ o} {t : 𝕋 o} {σ : Tree Γ f t}
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → (σ↓ : Tree↓ Γ (Σ↑ A B) f↓ σ)
      → (p : Pos t)
      → Inh↓ (Tree-snd↓ σ↓) p ↦ Cell-snd↓ (Inh↓ σ↓ p) 
    {-# REWRITE Inh-snd↓ #-}

    Tree-fst-η↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {o : 𝕆 n} {f : Frm Γ o} {t : 𝕋 o} 
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → {τ : Cell Γ f} (τ↓ : Cell↓ Γ (Σ↑ A B) f↓ τ)
      → Tree-fst↓ (η↓ f↓ τ↓) ↦ η↓ (Frm-fst↓ f↓) (Cell-fst↓ τ↓)
    {-# REWRITE Tree-fst-η↓ #-}

    Tree-snd-η↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {o : 𝕆 n} {f : Frm Γ o} {t : 𝕋 o}
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → {τ : Cell Γ f} (τ↓ : Cell↓ Γ (Σ↑ A B) f↓ τ)
      → Tree-snd↓ (η↓ f↓ τ↓) ↦ η↓ (Frm-snd↓ f↓) (Cell-snd↓ τ↓)
    {-# REWRITE Tree-snd-η↓ #-}

    Tree-fst-μ↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {o : 𝕆 n} {f : Frm Γ o} {t : 𝕋 o}
      → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
      → {σ : Tree Γ f t}
      → {δ : (p : Pos t) → Tree Γ (Typ σ p) (δₒ p) }
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → (σ↓ : Tree↓ Γ (Σ↑ A B) f↓ σ)
      → (δ↓ : (p : Pos t) → Tree↓ Γ (Σ↑ A B) (Typ↓ σ↓ p) (δ p))
      → Tree-fst↓ (μ↓ σ↓ δ↓) ↦ μ↓ (Tree-fst↓ σ↓) (λ p → Tree-fst↓ (δ↓ p)) 
    {-# REWRITE Tree-fst-μ↓ #-}

    Tree-snd-μ↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {o : 𝕆 n} {f : Frm Γ o} {t : 𝕋 o}
      → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
      → {σ : Tree Γ f t}
      → {δ : (p : Pos t) → Tree Γ (Typ σ p) (δₒ p) }
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → (σ↓ : Tree↓ Γ (Σ↑ A B) f↓ σ)
      → (δ↓ : (p : Pos t) → Tree↓ Γ (Σ↑ A B) (Typ↓ σ↓ p) (δ p))
      → Tree-snd↓ (μ↓ σ↓ δ↓) ↦ μ↓ (Tree-snd↓ σ↓) (λ p → Tree-snd↓ (δ↓ p))
    {-# REWRITE Tree-snd-μ↓ #-}

  Frm-fst↓ (■ b₀ ▸ b₁) = ■ fst b₀ ▸ fst b₁
  Frm-fst↓ (x ∥ σ↓ ▸ τ↓) = Frm-fst↓ x ∥ Tree-fst↓ σ↓ ▸ Cell-fst↓ τ↓

  Frm-snd↓ (■ b₀ ▸ b₁) = ■ snd b₀ ▸ snd b₁
  Frm-snd↓ (f↓ ∥ σ↓ ▸ τ↓) = Frm-snd↓ f↓ ∥ Tree-snd↓ σ↓ ▸ Cell-snd↓ τ↓

  Tree-fst↓ (nil↓ (a , b)) = nil↓ a
  Tree-fst↓ (cns↓ ρ↓ σ↓) = cns↓ (Cell-fst↓ ρ↓) (Tree-fst↓ σ↓)
  Tree-fst↓ (lf↓ f↓ τ↓) = lf↓ (Frm-fst↓ f↓) (Cell-fst↓ τ↓)
  Tree-fst↓ (nd↓ σ↓ τ↓ θ↓ δ↓ ε↓) =
    let σ↓₁ = Tree-fst↓ σ↓
        τ↓₁ = Cell-fst↓ τ↓
        θ↓₁ = Cell-fst↓ θ↓
        δ↓₁ p = Tree-fst↓ (δ↓ p)
        ε↓₁ p = Tree-fst↓ (ε↓ p)
    in nd↓ σ↓₁ τ↓₁ θ↓₁ δ↓₁ ε↓₁

  Tree-snd↓ (nil↓ (a , b)) = nil↓ b
  Tree-snd↓ (cns↓ ρ↓ σ↓) = cns↓ (Cell-snd↓ ρ↓) (Tree-snd↓ σ↓)
  Tree-snd↓ (lf↓ f↓ τ↓) = lf↓ (Frm-snd↓ f↓) (Cell-snd↓ τ↓)
  Tree-snd↓ (nd↓ σ↓ τ↓ θ↓ δ↓ ε↓) =
    let σ↓₁ = Tree-snd↓ σ↓
        τ↓₁ = Cell-snd↓ τ↓
        θ↓₁ = Cell-snd↓ θ↓
        δ↓₁ p = Tree-snd↓ (δ↓ p)
        ε↓₁ p = Tree-snd↓ (ε↓ p)
    in nd↓ σ↓₁ τ↓₁ θ↓₁ δ↓₁ ε↓₁
