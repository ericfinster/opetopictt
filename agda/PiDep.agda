{-# OPTIONS --without-K --rewriting #-}

open import Base
open import OpetopicType
open import OpetopicTypeOver
open import Sigma

module PiDep where

  -- Dependent Π
  
  Π↑ : {Γ : Set} (A : Γ → Set) (B : Σ Γ A → Set) → Γ → Set
  Π↑ A B γ = Π (A γ) (λ a → B (γ , a))

  Frm-ap↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
    → {n : ℕ} {γ₀ : Frm Γ n}
    → (π₀ : Frm↓ Γ (Π↑ A B) γ₀)
    → (a₀ : Frm↓ Γ A γ₀)
    → Frm↓ (Σ Γ A) B (Frm-pr γ₀ a₀)

  Tree-ap↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
    → {n : ℕ} {γ₀ : Frm Γ n} (γ : Tree Γ γ₀)
    → {π₀ : Frm↓ Γ (Π↑ A B) γ₀} (π : Tree↓ Γ (Π↑ A B) π₀ γ)
    → (a₀ : Frm↓ Γ A γ₀) (a : Tree↓ Γ A a₀ γ)
    → Tree↓ (Σ Γ A) B (Frm-ap↓ π₀ a₀) (Tree-pr γ a)
  
  postulate

    Cell-λ↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {γ₀ : Frm Γ n} {γ : Cell Γ γ₀}
      → {π₀ : Frm↓ Γ (Π↑ A B) γ₀}
      → (b : (a₀ : Frm↓ Γ A γ₀) (a : Cell↓ Γ A a₀ γ)
             → Cell↓ (Σ Γ A) B (Frm-ap↓ π₀ a₀) (Cell-pr γ a))
      → Cell↓ Γ (Π↑ A B) π₀ γ

    Cell-ap↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {γ₀ : Frm Γ n} {γ : Cell Γ γ₀}
      → {π₀ : Frm↓ Γ (Π↑ A B) γ₀} (π : Cell↓ Γ (Π↑ A B) π₀ γ)
      → {a₀ : Frm↓ Γ A γ₀} (a : Cell↓ Γ A a₀ γ)
      → Cell↓ (Σ Γ A) B (Frm-ap↓ π₀ a₀) (Cell-pr γ a) 

    Frm-ap-Typ↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {τ : Cell Γ f} {σ : Tree Γ f}
      → (f↓ : Frm↓ Γ (Π↑ A B) f) (f↓₁ : Frm↓ Γ A f)
      → (σ↓ : Tree↓ Γ (Π↑ A B) f↓ σ) (σ↓₁ : Tree↓ Γ A f↓₁ σ)
      → (p : Pos σ)
      → Frm-ap↓ (Typ↓ σ↓ p) (Typ↓ σ↓₁ p) ↦ Typ↓ (Tree-ap↓ σ σ↓ f↓₁ σ↓₁) p 
    {-# REWRITE Frm-ap-Typ↓ #-}

    Tree-ap-η↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {τ : Cell Γ f} {σ : Tree Γ f}
      → (f↓ : Frm↓ Γ (Π↑ A B) f) (f↓₁ : Frm↓ Γ A f)
      → (τ↓ : Cell↓ Γ (Π↑ A B) f↓ τ) (τ↓₁ : Cell↓ Γ A f↓₁ τ)
      →  Tree-ap↓ (η f τ) (η↓ f↓ τ↓) f↓₁ (η↓ f↓₁ τ↓₁)  ↦ η↓ (Frm-ap↓ f↓ f↓₁) (Cell-ap↓ τ↓ τ↓₁)
    {-# REWRITE Tree-ap-η↓ #-}

    Tree-ap-μ↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {τ : Cell Γ f} {σ : Tree Γ f}
      → {δ : (p : Pos σ) → Tree Γ (Typ σ p)}
      → (f↓ : Frm↓ Γ (Π↑ A B) f) (f↓₁ : Frm↓ Γ A f)
      → (σ↓ : Tree↓ Γ (Π↑ A B) f↓ σ) (σ↓₁ : Tree↓ Γ A f↓₁ σ)
      → (δ↓ : (p : Pos σ) → Tree↓ Γ (Π↑ A B) (Typ↓ σ↓ p) (δ p))
      → (δ↓₁ : (p : Pos σ) → Tree↓ Γ A (Typ↓ σ↓₁ p) (δ p))
      → (τ↓ : Cell↓ Γ (Π↑ A B) f↓ τ) (τ↓₁ : Cell↓ Γ A f↓₁ τ)
      →  Tree-ap↓ (μ σ δ) (μ↓ σ↓ δ↓) f↓₁ (μ↓ σ↓₁ δ↓₁)  ↦ μ↓ (Tree-ap↓ _ σ↓ _ σ↓₁) λ p → Tree-ap↓ _ (δ↓ p) _ (δ↓₁ p)
    {-# REWRITE Tree-ap-μ↓ #-}

    Cell-λ↓-ap↓  : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {τ : Cell Γ f}
      → (f↓ : Frm↓ Γ (Π↑ A B) f)
      → (τ↓ : Cell↓ Γ (Π↑ A B) f↓ τ)
      → Cell-λ↓ (λ f₁ τ₁ → Cell-ap↓ τ↓ τ₁) ↦ τ↓
    {-# REWRITE Cell-λ↓-ap↓  #-}
  
    Cell-ap-Inh↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {τ : Cell Γ f} {σ : Tree Γ f}
      → (f↓ : Frm↓ Γ (Π↑ A B) f) (f↓₁ : Frm↓ Γ A f)
      → (σ↓ : Tree↓ Γ (Π↑ A B) f↓ σ) (σ↓₁ : Tree↓ Γ A f↓₁ σ)
      → (p : Pos σ)
      → Cell-ap↓ (Inh↓ σ↓ p) (Inh↓ σ↓₁ p) ↦ Inh↓ (Tree-ap↓ σ σ↓ f↓₁ σ↓₁) p
    {-# REWRITE Cell-ap-Inh↓ #-}

  Frm-ap↓ ■ ■ = ■
  Frm-ap↓ (π₀ ∥ σ↓ ▸ τ↓) (a₀ ∥ σ↓₁ ▸ τ↓₁) =
    let f = Frm-ap↓ π₀ a₀
        σ = Tree-ap↓ _ σ↓ a₀ σ↓₁
        g f τ = Cell-ap↓ τ↓ τ
        τ = Cell-ap↓ (Cell-λ↓ g) τ↓₁
    in f ∥ σ ▸ τ

  Tree-ap↓ .(ob _) (ob↓ τ↓) .■ (ob↓ τ↓₁) = ob↓ (Cell-ap↓ τ↓ τ↓₁)
  Tree-ap↓ .(lf _ _) (lf↓ f↓ τ↓) .(f↓₁ ∥ η↓ f↓₁ τ↓₁ ▸ τ↓₁) (lf↓ f↓₁ τ↓₁) = lf↓ (Frm-ap↓ f↓ f↓₁) (Cell-ap↓ τ↓ τ↓₁)
  Tree-ap↓ (nd _ _ _ _ _ _) (nd↓ π τ↓ θ↓ δ↓ ε↓) .(_ ∥ μ↓ a δ↓₁ ▸ τ↓₁) (nd↓ a τ↓₁ θ↓₁ δ↓₁ ε↓₁) =
    let ϕ p = Tree-ap↓ _ (δ↓ p) _ (δ↓₁ p)
        ψ p = Tree-ap↓ _ (ε↓ p) _ (ε↓₁ p)
    in nd↓ (Tree-ap↓ _ π _ a) (Cell-ap↓ τ↓ τ↓₁) (Cell-ap↓ θ↓ θ↓₁) ϕ ψ
