{-# OPTIONS --without-K --rewriting #-}

open import Base
open import Opetopes
open import OpetopicType
open import OpetopicTypeOver
open import Cell

module CellCellOver where

  -- Cells in a Cell↓ are cells over degeneracies.

  Frm-degen : {A : Set} {B : A → Set}
    → {n m : ℕ} {o : 𝕆 n} {oc : 𝕆 m}
    → {f : Frm A o} (ζ : Cell A f)
    → {f↓ : Frm↓ A B f}
    → (fc : Frm (Cell↓ A B f↓ ζ) oc)
    → Frm↓ A B (Frm-⊕ f (Frm-refl ζ oc))

  Tree-degen : {A : Set} {B : A → Set}
    → {n m : ℕ} {o : 𝕆 n} {oc : 𝕆 m} {t : 𝕋 oc}
    → {f : Frm A o} (ζ : Cell A f)
    → {f↓ : Frm↓ A B f}
    → {fc : Frm (Cell↓ A B f↓ ζ) oc}
    → (σ : Tree (Cell↓ A B f↓ ζ) fc t)
    → Tree↓ A B (Frm-degen ζ fc) (Tree-⊕ f (Tree-refl ζ t))

  postulate

    Cell-Cell↓ : {A : Set} {B : A → Set}
      → {n m : ℕ} {o : 𝕆 n} {oc : 𝕆 m}
      → {f : Frm A o} (ζ : Cell A f)
      → {f↓ : Frm↓ A B f}
      → (fc : Frm (Cell↓ A B f↓ ζ) oc)
      → Cell (Cell↓ A B f↓ ζ) fc ↦ Cell↓ A B (Frm-degen ζ fc) (Cell-refl ζ oc)
    {-# REWRITE Cell-Cell↓ #-}

    Tree-degen-typ : {A : Set} {B : A → Set}
      → {n m : ℕ} {o : 𝕆 n} {oc : 𝕆 m} {t : 𝕋 oc}
      → {f : Frm A o} (ζ : Cell A f)
      → {f↓ : Frm↓ A B f}
      → {fc : Frm (Cell↓ A B f↓ ζ) oc}
      → (σ : Tree (Cell↓ A B f↓ ζ) fc t) (p : Pos (o ⊕t t))
      → Typ↓ (Tree-degen ζ σ) p ↦ Frm-degen ζ (Typ σ (o ⊝p p))
    {-# REWRITE Tree-degen-typ #-}
    
    Tree-degen-inh : {A : Set} {B : A → Set}
      → {n m : ℕ} {o : 𝕆 n} {oc : 𝕆 m} {t : 𝕋 oc}
      → {f : Frm A o} (ζ : Cell A f)
      → {f↓ : Frm↓ A B f}
      → {fc : Frm (Cell↓ A B f↓ ζ) oc}
      → (σ : Tree (Cell↓ A B f↓ ζ) fc t) (p : Pos (o ⊕t t))
      → Inh↓ (Tree-degen ζ σ) p ↦ Inh σ (o ⊝p p)
    {-# REWRITE Tree-degen-inh #-}

    Tree-degen-η : {A : Set} {B : A → Set}
      → {n m : ℕ} {o : 𝕆 n} {oc : 𝕆 m} 
      → {f : Frm A o} (ζ : Cell A f)
      → {f↓ : Frm↓ A B f}
      → {fc : Frm (Cell↓ A B f↓ ζ) oc}
      → (τ : Cell (Cell↓ A B f↓ ζ) fc)
      → Tree-degen ζ (η fc τ) ↦ η↓ (Frm-degen ζ fc) τ
    {-# REWRITE Tree-degen-η #-}

    Tree-degen-μ : {A : Set} {B : A → Set}
      → {n m : ℕ} {o : 𝕆 n} {oc : 𝕆 m} {t : 𝕋 oc}
      → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
      → {f : Frm A o} (ζ : Cell A f)
      → {f↓ : Frm↓ A B f}
      → {fc : Frm (Cell↓ A B f↓ ζ) oc}
      → (σ : Tree (Cell↓ A B f↓ ζ) fc t)
      → (δ : (p : Pos t) → Tree (Cell↓ A B f↓ ζ) (Typ σ p) (δₒ p))
      → Tree-degen ζ (μ σ δ) ↦ μ↓ (Tree-degen ζ σ) (λ p → Tree-degen ζ (δ (o ⊝p p)))
    {-# REWRITE Tree-degen-μ #-}

  Frm-degen ζ {f↓ = f↓} (□ a₀ ▹ a₁) = f↓ ∥ η↓ f↓ a₀ ▸ a₁
  Frm-degen ζ (fc ∥ σ ▹ τ) = Frm-degen ζ fc ∥ Tree-degen ζ σ ▸ τ

  Tree-degen ζ {f↓ = f↓} (nil a) = lf↓ f↓ a
  Tree-degen ζ {f↓ = f↓} (cns {a₀ = a₀} {a₁ = a₁} {a₂ = a₂} ρ σ) =
    nd↓ (η↓ f↓ a₁) a₂ ρ (λ _ → η↓ f↓ a₀) (λ _ → Tree-degen ζ σ) 
  Tree-degen ζ (lf f τ) = lf↓ (Frm-degen ζ f) τ
  Tree-degen {o = o} ζ (nd σ τ θ δ ε) =
    nd↓ (Tree-degen ζ σ) τ θ
        (λ p → Tree-degen ζ (δ (o ⊝p p)))
        (λ p → Tree-degen ζ (ε (o ⊝p p)))

