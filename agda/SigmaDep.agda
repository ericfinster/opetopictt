{-# OPTIONS --without-K --rewriting #-}

open import Base
open import OpetopicType
open import OpetopicTypeOver
open import Sigma

module SigmaDep where

  Σ↑ : {Γ : Set} (A : Γ → Set) (B : Σ Γ A → Set) → Γ → Set
  Σ↑ A B γ = Σ (A γ) (λ a → B (γ , a))

  Frm-pr↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
    → {n : ℕ} {f : Frm Γ n}
    → (f↓ : Frm↓ Γ A f)
    → (f↓₁ : Frm↓ (Σ Γ A) B (Frm-pr f f↓))
    → Frm↓ Γ (Σ↑ A B) f 

  Frm-fst↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
    → {n : ℕ} {f : Frm Γ n}
    → Frm↓ Γ (Σ↑ A B) f
    → Frm↓ Γ A f

  Frm-snd↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
    → {n : ℕ} {f : Frm Γ n}
    → (f↓ : Frm↓ Γ (Σ↑ A B) f)
    → Frm↓ (Σ Γ A) B (Frm-pr f (Frm-fst↓ f↓))

  Tree-pr↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
    → {n : ℕ} {f : Frm Γ n} {σ : Tree Γ f}
    → {f↓ : Frm↓ Γ A f}
    → {f↓₁ : Frm↓ (Σ Γ A) B (Frm-pr f f↓)}
    → (σ↓ : Tree↓ Γ A f↓ σ)
    → (σ↓₁ : Tree↓ (Σ Γ A) B f↓₁ (Tree-pr σ σ↓))
    → Tree↓ Γ (Σ↑ A B) (Frm-pr↓ f↓ f↓₁) σ 

  Tree-fst↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
    → {n : ℕ} {f : Frm Γ n} {σ : Tree Γ f}
    → {f↓ : Frm↓ Γ (Σ↑ A B) f}
    → Tree↓ Γ (Σ↑ A B) f↓ σ
    → Tree↓ Γ A (Frm-fst↓ f↓) σ

  Tree-snd↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
    → {n : ℕ} {f : Frm Γ n} {σ : Tree Γ f}
    → {f↓ : Frm↓ Γ (Σ↑ A B) f}
    → (σ↓ : Tree↓ Γ (Σ↑ A B) f↓ σ)
    → Tree↓ (Σ Γ A) B (Frm-snd↓ f↓) (Tree-pr σ (Tree-fst↓ σ↓))
      

  postulate    
  
    Cell-pr↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {τ : Cell Γ f}
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → (τ↓ : Cell↓ Γ A (Frm-fst↓ f↓) τ)
      → (τ↓₁ : Cell↓ (Σ Γ A) B (Frm-snd↓ f↓) (Cell-pr τ τ↓))
      → Cell↓ Γ (Σ↑ A B) f↓ τ

    Cell-fst↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {τ : Cell Γ f}
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → Cell↓ Γ (Σ↑ A B) f↓ τ
      → Cell↓ Γ A (Frm-fst↓ f↓) τ

    Cell-snd↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {τ : Cell Γ f}
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → (σ↓ : Cell↓ Γ (Σ↑ A B) f↓ τ)
      → Cell↓ (Σ Γ A) B (Frm-snd↓ f↓) (Cell-pr τ (Cell-fst↓ σ↓))

    -- Cells equations
    Cell-fst-β↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {τ : Cell Γ f}
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → (τ↓ : Cell↓ Γ A (Frm-fst↓ f↓) τ)
      → (τ↓₁ : Cell↓ (Σ Γ A) B (Frm-snd↓ f↓) (Cell-pr τ τ↓))
      → Cell-fst↓ (Cell-pr↓ τ↓ τ↓₁) ↦ τ↓
    {-# REWRITE Cell-fst-β↓ #-}

    Cell-snd-β↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {τ : Cell Γ f}
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → (τ↓ : Cell↓ Γ A (Frm-fst↓ f↓) τ)
      → (τ↓₁ : Cell↓ (Σ Γ A) B (Frm-snd↓ f↓) (Cell-pr τ τ↓))
      → Cell-snd↓ (Cell-pr↓ τ↓ τ↓₁) ↦ τ↓₁
    {-# REWRITE Cell-snd-β↓ #-}

    Cell-pr-β↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {τ : Cell Γ f}
      → (f↓ : Frm↓ Γ (Σ↑ A B) f )
      → (τ↓ : Cell↓ Γ (Σ↑ A B) f↓ τ)
      → Cell-pr↓ (Cell-fst↓ τ↓) (Cell-snd↓ τ↓) ↦ τ↓
    {-# REWRITE Cell-pr-β↓ #-}

    -- Frm equations
    Frm-pr-β↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n}
      → (f↓ : Frm↓ Γ (Σ↑ A B) f)
      → Frm-pr↓ (Frm-fst↓ f↓) (Frm-snd↓ f↓) ↦ f↓
    {-# REWRITE Frm-pr-β↓ #-}

    Frm-fst-β↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n}
      → (f↓ : Frm↓ Γ A f)
      → (f↓₁ : Frm↓ (Σ Γ A) B (Frm-pr f f↓))
      → Frm-fst↓ (Frm-pr↓ f↓ f↓₁) ↦ f↓
    {-# REWRITE Frm-fst-β↓ #-}
    
    Frm-snd-β↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n}
      → (f↓ : Frm↓ Γ A f)
      → (f↓₁ : Frm↓ (Σ Γ A) B (Frm-pr f f↓))
      → Frm-snd↓ (Frm-pr↓ f↓ f↓₁) ↦ f↓₁
    {-# REWRITE Frm-snd-β↓ #-}

    -- Typ/Inh equations
    Typ-pr↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {σ : Tree Γ f}
      → {f↓ : Frm↓ Γ A f} {f↓₁ : Frm↓ (Σ Γ A) B (Frm-pr f f↓)}
      → (σ↓ : Tree↓ Γ A f↓ σ) (σ↓₁ : Tree↓ (Σ Γ A) B f↓₁ (Tree-pr σ σ↓))
      → (p : Pos σ)
      → Typ↓ (Tree-pr↓ σ↓ σ↓₁) p ↦ Frm-pr↓ (Typ↓ σ↓ p) (Typ↓ σ↓₁ p)
    {-# REWRITE Typ-pr↓ #-}

    Inh-pr↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {σ : Tree Γ f}
      → {f↓ : Frm↓ Γ A f} {f↓₁ : Frm↓ (Σ Γ A) B (Frm-pr f f↓)}
      → (σ↓ : Tree↓ Γ A f↓ σ) (σ↓₁ : Tree↓ (Σ Γ A) B f↓₁ (Tree-pr σ σ↓))
      → (p : Pos σ)
      → Inh↓ (Tree-pr↓ σ↓ σ↓₁) p ↦ Cell-pr↓ (Inh↓ σ↓ p) (Inh↓ σ↓₁ p)
    {-# REWRITE Inh-pr↓ #-}

    Typ-fst↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {σ : Tree Γ f}
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → (σ↓ : Tree↓ Γ (Σ↑ A B) f↓ σ)
      → (p : Pos σ)
      → Typ↓ (Tree-fst↓ σ↓) p ↦ Frm-fst↓ (Typ↓ σ↓ p) 
    {-# REWRITE Typ-fst↓ #-}

    Inh-fst↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {σ : Tree Γ f}
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → (σ↓ : Tree↓ Γ (Σ↑ A B) f↓ σ)
      → (p : Pos σ)
      → Inh↓ (Tree-fst↓ σ↓) p ↦ Cell-fst↓ (Inh↓ σ↓ p) 
    {-# REWRITE Inh-fst↓ #-}

    Typ-snd↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {σ : Tree Γ f}
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → (σ↓ : Tree↓ Γ (Σ↑ A B) f↓ σ) (p : Pos σ)
      → Typ↓ (Tree-snd↓ σ↓) p ↦ Frm-snd↓ (Typ↓ σ↓ p) 
    {-# REWRITE Typ-snd↓ #-}

    Inh-snd↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {σ : Tree Γ f}
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → (σ↓ : Tree↓ Γ (Σ↑ A B) f↓ σ)
      → (p : Pos σ)
      → Inh↓ (Tree-snd↓ σ↓) p ↦ Cell-snd↓ (Inh↓ σ↓ p) 
    {-# REWRITE Inh-snd↓ #-}

    -- Tree equations
    Tree-fst-β↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {σ : Tree Γ f}
      → {f↓ : Frm↓ Γ A f}
      → {f↓₁ : Frm↓ (Σ Γ A) B (Frm-pr f f↓)}
      → (σ↓ : Tree↓ Γ A f↓ σ)
      → (σ↓₁ : Tree↓ (Σ Γ A) B f↓₁ (Tree-pr σ σ↓))
      → Tree-fst↓ (Tree-pr↓ σ↓ σ↓₁) ↦ σ↓
    {-# REWRITE Tree-fst-β↓ #-}

    Tree-snd-β↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {σ : Tree Γ f}
      → {f↓ : Frm↓ Γ A f}
      → {f↓₁ : Frm↓ (Σ Γ A) B (Frm-pr f f↓)}
      → (σ↓ : Tree↓ Γ A f↓ σ)
      → (σ↓₁ : Tree↓ (Σ Γ A) B f↓₁ (Tree-pr σ σ↓))
      → Tree-snd↓ (Tree-pr↓ σ↓ σ↓₁) ↦ σ↓₁
    {-# REWRITE Tree-snd-β↓ #-}      
     
    Tree-pr-β↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {σ : Tree Γ f}
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → (σ↓ : Tree↓ Γ (Σ↑ A B) f↓ σ)
      → Tree-pr↓ (Tree-fst↓ σ↓) (Tree-snd↓ σ↓) ↦ σ↓
    {-# REWRITE Tree-pr-β↓ #-}

    Tree-pr-η↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {τ : Cell Γ f}
      → {f↓ : Frm↓ Γ A f} {f↓₁ : Frm↓ (Σ Γ A) B (Frm-pr f f↓)}
      → (τ↓ : Cell↓ Γ A f↓ τ)
      → (τ↓₁ : Cell↓ (Σ Γ A) B f↓₁ (Cell-pr τ τ↓))
      → Tree-pr↓ (η↓ f↓ τ↓) (η↓ f↓₁ τ↓₁) ↦ η↓ (Frm-pr↓ f↓ f↓₁) (Cell-pr↓ τ↓ τ↓₁)
    {-# REWRITE Tree-pr-η↓ #-}

    Tree-fst-η↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {σ : Tree Γ f} {τ : Cell Γ f}
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → (τ↓ : Cell↓ Γ (Σ↑ A B) f↓ τ)
      → Tree-fst↓ (η↓ f↓ τ↓) ↦ η↓ (Frm-fst↓ f↓) (Cell-fst↓ τ↓)
    {-# REWRITE Tree-fst-η↓ #-}

    Tree-snd-η↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {σ : Tree Γ f} {τ : Cell Γ f}
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → (τ↓ : Cell↓ Γ (Σ↑ A B) f↓ τ)
      → Tree-snd↓ (η↓ f↓ τ↓) ↦ η↓ (Frm-snd↓ f↓) (Cell-snd↓ τ↓)
    {-# REWRITE Tree-snd-η↓ #-}

    Tree-pr-μ↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {σ : Tree Γ f}
      → {δ : (p : Pos σ) → Tree Γ (Typ σ p) }
      → {f↓ : Frm↓ Γ A f} {f↓₁ : Frm↓ (Σ Γ A) B (Frm-pr f f↓)}
      → (σ↓ : Tree↓ Γ A f↓ σ) (σ↓₁ : Tree↓ (Σ Γ A) B f↓₁ (Tree-pr σ σ↓))
      → (δ↓ : (p : Pos σ) → Tree↓ Γ A (Typ↓ σ↓ p) (δ p))
      → (δ↓₁ : (p : Pos σ) → Tree↓ (Σ Γ A) B (Typ↓ σ↓₁ p) (Tree-pr (δ p) (δ↓ p)))
      → Tree-pr↓ (μ↓ σ↓ δ↓) (μ↓ σ↓₁ δ↓₁) ↦ μ↓ (Tree-pr↓ σ↓ σ↓₁) (λ p → Tree-pr↓ (δ↓ p) (δ↓₁ p))
    {-# REWRITE Tree-pr-μ↓ #-}

    Tree-fst-μ↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {σ : Tree Γ f}
      → {δ : (p : Pos σ) → Tree Γ (Typ σ p) }
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → (σ↓ : Tree↓ Γ (Σ↑ A B) f↓ σ)
      → (δ↓ : (p : Pos σ) → Tree↓ Γ (Σ↑ A B) (Typ↓ σ↓ p) (δ p))
      → Tree-fst↓ (μ↓ σ↓ δ↓) ↦ μ↓ (Tree-fst↓ σ↓) (λ p → Tree-fst↓ (δ↓ p)) 
    {-# REWRITE Tree-fst-μ↓ #-}

    Tree-snd-μ↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {f : Frm Γ n} {σ : Tree Γ f}
      → {δ : (p : Pos σ) → Tree Γ (Typ σ p) }
      → {f↓ : Frm↓ Γ (Σ↑ A B) f}
      → (σ↓ : Tree↓ Γ (Σ↑ A B) f↓ σ)
      → (δ↓ : (p : Pos σ) → Tree↓ Γ (Σ↑ A B) (Typ↓ σ↓ p) (δ p))
      → Tree-snd↓ (μ↓ σ↓ δ↓) ↦ μ↓ (Tree-snd↓ σ↓) (λ p → Tree-snd↓ (δ↓ p))
    {-# REWRITE Tree-snd-μ↓ #-}

  Frm-pr↓ ■ ■ = ■
  Frm-pr↓ (f↓ ∥ σ↓ ▸ τ↓) (f↓₁ ∥ σ↓₁ ▸ τ↓₁) =
    Frm-pr↓ f↓ f↓₁ ∥ Tree-pr↓ σ↓ σ↓₁ ▸ Cell-pr↓ τ↓ τ↓₁

  Frm-fst↓ ■ = ■
  Frm-fst↓ (x ∥ σ↓ ▸ τ↓) = Frm-fst↓ x ∥ Tree-fst↓ σ↓ ▸ Cell-fst↓ τ↓

  Frm-snd↓ ■ = ■
  Frm-snd↓ (x ∥ σ↓ ▸ τ↓) = Frm-snd↓ x ∥ Tree-snd↓ σ↓ ▸ Cell-snd↓ τ↓

  Tree-pr↓ (ob↓ τ↓) (ob↓ τ↓₁) = ob↓ (Cell-pr↓ τ↓ τ↓₁)
  Tree-pr↓ (lf↓ f↓ τ↓) (lf↓ f↓₁ τ↓₁) = lf↓ (Frm-pr↓ f↓ f↓₁) (Cell-pr↓ τ↓ τ↓₁)
  Tree-pr↓ (nd↓ σ↓ τ↓ θ↓ δ↓ ε↓) (nd↓ σ↓₁ τ↓₁ θ↓₁ δ↓₁ ε↓₁) =
    let ϕ p = Tree-pr↓ (δ↓ p) (δ↓₁ p)
        ψ p = Tree-pr↓ (ε↓ p) (ε↓₁ p)
    in nd↓ (Tree-pr↓ σ↓ σ↓₁) (Cell-pr↓ τ↓ τ↓₁) (Cell-pr↓ θ↓ θ↓₁) ϕ ψ 

  Tree-fst↓ (ob↓ τ↓) = ob↓ (Cell-fst↓ τ↓)
  Tree-fst↓ (lf↓ f↓ τ↓) = lf↓ (Frm-fst↓ f↓) (Cell-fst↓ τ↓)
  Tree-fst↓ (nd↓ x τ↓ θ↓ δ↓ ε↓) =
    let x₁ = Tree-fst↓ x
        τ↑₁ = Cell-fst↓ τ↓
        θ↓₁ = Cell-fst↓ θ↓
        δ↓₁ p = Tree-fst↓ (δ↓ p)
        ε↓₁ p = Tree-fst↓ (ε↓ p)
    in nd↓ x₁ τ↑₁ θ↓₁ δ↓₁ ε↓₁

  Tree-snd↓ (ob↓ τ↓) = ob↓ (Cell-snd↓ τ↓)
  Tree-snd↓ (lf↓ f↓ τ↓) = lf↓ (Frm-snd↓ f↓) (Cell-snd↓ τ↓)
  Tree-snd↓ (nd↓ x τ↓ θ↓ δ↓ ε↓) =
    let x₁ = Tree-snd↓ x
        τ↑₁ = Cell-snd↓ τ↓
        θ↓₁ = Cell-snd↓ θ↓
        δ↓₁ p = Tree-snd↓ (δ↓ p)
        ε↓₁ p = Tree-snd↓ (ε↓ p)
    in nd↓ x₁ τ↑₁ θ↓₁ δ↓₁ ε↓₁
