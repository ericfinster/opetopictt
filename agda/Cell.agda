{-# OPTIONS --without-K --rewriting #-}

open import Base
open import OpetopicType
open import OpetopicTypeOver

module Cell where

  --
  --  Cell concatenation
  --
  
  Frm-concat : {A : Set} {n m : ℕ} 
    → (f : Frm A n) (fc : Frm (Cell A f) m)
    → Frm A (m + n)

  Tree-concat : {A : Set} {n m : ℕ} 
    → (f : Frm A n) {fc : Frm (Cell A f) m}
    → (σ : Tree (Cell A f) fc)
    → Tree A (Frm-concat f fc)

  postulate

    Cell-concat : {A : Set} {n m : ℕ} 
      → {f : Frm A n} {fc : Frm (Cell A f) m}
      → (τ : Cell (Cell A f) fc)
      → Cell A (Frm-concat f fc)

    Pos-concat : {A : Set} {n m : ℕ}
      → (f : Frm A n) (fc : Frm (Cell A f) m)
      → (σ : Tree (Cell A f) fc)
      → Pos (Tree-concat f σ) ↦ Pos σ 
    {-# REWRITE Pos-concat #-}

    Typ-concat : {A : Set} {n m : ℕ}
      → (f : Frm A n) (fc : Frm (Cell A f) m)
      → (σ : Tree (Cell A f) fc) (p : Pos σ)
      → Typ (Tree-concat f σ) p ↦ Frm-concat f (Typ σ p)
    {-# REWRITE Typ-concat #-}

    Inh-concat : {A : Set} {n m : ℕ}
      → (f : Frm A n) (fc : Frm (Cell A f) m)
      → (σ : Tree (Cell A f) fc) (p : Pos σ)
      → Inh (Tree-concat f σ) p ↦ Cell-concat (Inh σ p)
    {-# REWRITE Inh-concat #-}

    Tree-concat-η : {A : Set} {n m : ℕ}
      → {f : Frm A n} {fc : Frm (Cell A f) m}
      → (τ : Cell (Cell A f) fc)
      → Tree-concat f (η fc τ) ↦ η (Frm-concat f fc) (Cell-concat τ) 
    {-# REWRITE Tree-concat-η #-}

    Tree-concat-μ : {A : Set} {n m : ℕ}
      → {f : Frm A n} {fc : Frm (Cell A f) m}
      → (σ : Tree (Cell A f) fc)
      → (δ : (p : Pos σ) → Tree (Cell A f) (Typ σ p))
      → Tree-concat f (μ σ δ) ↦ μ (Tree-concat f σ) (λ p → Tree-concat f (δ p))
    {-# REWRITE Tree-concat-μ #-}
    
  Frm-concat f ● = f
  Frm-concat f (fc ∣ σ ▸ τ) =
    Frm-concat f fc ∣ Tree-concat f σ ▸ Cell-concat τ

  Tree-concat f (ob τ) = η _ [ τ ]↓
  Tree-concat f (lf fc τ) =
    lf (Frm-concat f fc) (Cell-concat τ)
  Tree-concat f (nd fc σ τ θ δ ε) =
    nd (Frm-concat f fc) (Tree-concat f σ)
       (Cell-concat τ) (Cell-concat θ)
       (λ p → Tree-concat f (δ p))
       (λ p → Tree-concat f (ε p))

  -- Low-dimensional rewrites
  postulate

    Cell-concat-● : {A : Set} {n : ℕ}
      → (f : Frm A n) (τ : Cell (Cell A f) ●)
      → Cell-concat τ ↦ [ τ ]↓
    {-# REWRITE Cell-concat-● #-}

  --
  --  Cells-over-cells are commutative triangles
  --

  postulate
  
    Cell-triangle : {A : Set} 
      → {n : ℕ} {f : Frm A n} (σ : Tree A f)
      → (τ₀ : Cell A f) (θ₀ : Cell A (f ∣ σ ▸ τ₀))
      → (τ₁ : Cell A f) (θ₁ : Cell A (f ∣ σ ▸ τ₁))
      → (ϕ : Cell (Cell A f) (● ∣ ob [ τ₀ ]↑ ▸ [ τ₁ ]↑))
      → (ψ : Cell A (f ∣ σ ▸ τ₁ ∣ nd f (η f τ₀) τ₁ (Cell-concat ϕ) (λ p → σ) (λ p → η (f ∣ σ ▸ τ₀) θ₀) ▸ θ₁)) 
      → Cell↓ (Cell A f) (λ τ → Cell A (f ∣ σ ▸ τ))
              {f = ● ∣ ob [ τ₀ ]↑ ▸ [ τ₁ ]↑} (■ ∥ ob↓ ⟦ _ ∣ θ₀ ⟧↑ ▸ ⟦ _ ∣ θ₁ ⟧↑) ϕ

