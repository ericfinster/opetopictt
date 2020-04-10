{-# OPTIONS --without-K --rewriting #-}

open import Base
open import Opetopes
open import OpetopicType
open import OpetopicTypeOver

module Cell where

  --
  --  Cell concatenation
  --
  
  Frm-⊕ : {A : Set}
    → {m n : ℕ} {o₀ : 𝕆 m} {o₁ : 𝕆 n}
    → (f : Frm A o₀) (fc : Frm (Cell A f) o₁)
    → Frm A (o₀ ⊕ o₁)

  Tree-⊕ : {A : Set}
    → {m n : ℕ} {o₀ : 𝕆 m} {o₁ : 𝕆 n} {t : 𝕋 o₁}
    → (f : Frm A o₀) {fc : Frm (Cell A f) o₁}
    → Tree (Cell A f) fc t → Tree A (Frm-⊕ f fc) (o₀ ⊕t t)

  postulate

    Cell-Cell : {A : Set} {n m : ℕ} 
      → {m n : ℕ} {o₀ : 𝕆 m} {o₁ : 𝕆 n}
      → (f : Frm A o₀) (fc : Frm (Cell A f) o₁)
      → Cell (Cell A f) fc ↦ Cell A (Frm-⊕ f fc)
    {-# REWRITE Cell-Cell #-}

    Tree-⊕-typ : {A : Set}
      → {m n : ℕ} {o₀ : 𝕆 m} {o₁ : 𝕆 n} {t : 𝕋 o₁}
      → (f : Frm A o₀) {fc : Frm (Cell A f) o₁}
      → (σ : Tree (Cell A f) fc t) (p : Pos (o₀ ⊕t t))
      → Typ (Tree-⊕ f σ) p ↦ Frm-⊕ f (Typ σ (o₀ ⊝p p))
    {-# REWRITE Tree-⊕-typ #-}
    
    Tree-⊕-inh : {A : Set}
      → {m n : ℕ} {o₀ : 𝕆 m} {o₁ : 𝕆 n} {t : 𝕋 o₁}
      → (f : Frm A o₀) {fc : Frm (Cell A f) o₁}
      → (σ : Tree (Cell A f) fc t) (p : Pos (o₀ ⊕t t))
      → Inh (Tree-⊕ f σ) p ↦ Inh σ (o₀ ⊝p p)
    {-# REWRITE Tree-⊕-inh #-}

    Tree-⊕-η : {A : Set}
      → {m n : ℕ} {o₀ : 𝕆 m} {o₁ : 𝕆 n} 
      → (f : Frm A o₀) {fc : Frm (Cell A f) o₁}
      → (τ : Cell (Cell A f) fc)
      → Tree-⊕ f (η fc τ) ↦ η (Frm-⊕ f fc) τ
    {-# REWRITE Tree-⊕-η #-}

    Tree-⊕-μ : {A : Set}
      → {m n : ℕ} {o₀ : 𝕆 m} {o₁ : 𝕆 n} {t : 𝕋 o₁}
      → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
      → (f : Frm A o₀) {fc : Frm (Cell A f) o₁}
      → (σ : Tree (Cell A f) fc t)
      → (δ : (p : Pos t) → Tree (Cell A f) (Typ σ p) (δₒ p))
      → Tree-⊕ f (μ σ δ) ↦ μ (Tree-⊕ f σ) (λ p → Tree-⊕ f (δ (o₀ ⊝p p)))
    {-# REWRITE Tree-⊕-μ #-}

  Frm-⊕ f (□ a₀ ▹ a₁) = f ∥ η f a₀ ▹ a₁
  Frm-⊕ f (fc ∥ σ ▹ τ) = Frm-⊕ f fc ∥ Tree-⊕ f σ ▹ τ
  
  Tree-⊕ f (nil a) = lf f a
  Tree-⊕ f (cns {a₀ = a₀} {a₁ = a₁} {a₂ = a₂} ρ σ) =
    nd (η f a₁) a₂ ρ (λ _ → η f a₀) (λ _ → Tree-⊕ f σ)
  Tree-⊕ f (lf fc τ) = lf (Frm-⊕ f fc) τ
  Tree-⊕ {o₀ = o₀} f (nd σ τ θ δ ε) = nd (Tree-⊕ f σ) τ θ
    (λ p → Tree-⊕ f (δ (o₀ ⊝p p)))
    (λ p → Tree-⊕ f (ε (o₀ ⊝p p)))

