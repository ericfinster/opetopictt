{-# OPTIONS --without-K --rewriting #-}

open import Base
open import OpetopicType
open import OpetopicTypeOver

module Sigma where

  -- Rules for non-dependent Σ
  -- (i.e. context extension)

  Frm-pr : {A : Set} {B : A → Set}
    → {n : ℕ} (f : Frm A n) (f↓ : Frm↓ A B f)
    → Frm (Σ A B) n
    
  Frm-fst : {A : Set} {B : A → Set}
    → {n : ℕ} (f : Frm (Σ A B) n)
    → Frm A n

  Frm-snd : {A : Set} {B : A → Set}
    → {n : ℕ} (f : Frm (Σ A B) n)
    → Frm↓ A B (Frm-fst f)

  Tree-pr : {A : Set} {B : A → Set}
    → {n : ℕ} {f : Frm A n} {f↓ : Frm↓ A B f}
    → (σ : Tree A f) (σ↓ : Tree↓ A B f↓ σ)
    → Tree (Σ A B) (Frm-pr f f↓)

  Tree-fst : {A : Set} {B : A → Set}
    → {n : ℕ} {f : Frm (Σ A B) n}
    → Tree (Σ A B) f → Tree A (Frm-fst f)

  Tree-snd : {A : Set} {B : A → Set}
    → {n : ℕ} {f : Frm (Σ A B) n}
    → (σ : Tree (Σ A B) f)
    → Tree↓ A B (Frm-snd f) (Tree-fst σ)
    
  postulate

    Cell-pr : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm A n} {f↓ : Frm↓ A B f}
      → (a : Cell A f) (b : Cell↓ A B f↓ a)
      → Cell (Σ A B) (Frm-pr f f↓)
      
    Cell-fst : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm (Σ A B) n}
      → Cell (Σ A B) f → Cell A (Frm-fst f)

    Cell-snd : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm (Σ A B) n}
      → (τ : Cell (Σ A B) f)
      → Cell↓ A B (Frm-snd f) (Cell-fst τ)

  Frm-pr ● ■ = ●
  Frm-pr (f ∣ σ ▸ τ) (f↓ ∥ σ↓ ▸ τ↓) =
    Frm-pr f f↓ ∣ Tree-pr σ σ↓ ▸ Cell-pr τ τ↓

  Frm-fst ● = ●
  Frm-fst (f ∣ σ ▸ τ) = Frm-fst f ∣ Tree-fst σ ▸ Cell-fst τ
  
  Frm-snd ● = ■
  Frm-snd (f ∣ σ ▸ τ) = Frm-snd f ∥ Tree-snd σ ▸ Cell-snd τ

  postulate

    -- Pos/Typ/Inh equations
    Pos-pr : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm A n} {f↓ : Frm↓ A B f}
      → (σ : Tree A f) (σ↓ : Tree↓ A B f↓ σ)
      → Pos (Tree-pr σ σ↓) ↦ Pos σ
    {-# REWRITE Pos-pr #-}

    Typ-pr : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm A n} {f↓ : Frm↓ A B f}
      → (σ : Tree A f) (σ↓ : Tree↓ A B f↓ σ)
      → (p : Pos σ)
      → Typ (Tree-pr σ σ↓) p ↦ Frm-pr (Typ σ p) (Typ↓ σ↓ p)
    {-# REWRITE Typ-pr #-}

    Inh-pr : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm A n} {f↓ : Frm↓ A B f}
      → (σ : Tree A f) (σ↓ : Tree↓ A B f↓ σ)
      → (p : Pos σ)
      → Inh (Tree-pr σ σ↓) p ↦ Cell-pr (Inh σ p) (Inh↓ σ↓ p)
    {-# REWRITE Inh-pr #-}

    -- Should this equaltion be in the other direction?
    Pos-fst : {A : Set} {B : A → Set}
      → {n : ℕ} (f : Frm (Σ A B) n) (σ : Tree (Σ A B) f)
      → Pos (Tree-fst σ) ↦ Pos σ 
    {-# REWRITE Pos-fst #-}

    Typ-fst : {A : Set} {B : A → Set}
      → {n : ℕ} (f : Frm (Σ A B) n)
      → (σ : Tree (Σ A B) f) (p : Pos σ)
      → Typ (Tree-fst σ) p ↦ Frm-fst (Typ σ p) 
    {-# REWRITE Typ-fst #-}

    Inh-fst : {A : Set} {B : A → Set}
      → {n : ℕ} (f : Frm (Σ A B) n)
      → (σ : Tree (Σ A B) f) (p : Pos σ)
      → Inh (Tree-fst σ) p ↦ Cell-fst (Inh σ p) 
    {-# REWRITE Inh-fst #-}

    -- Frm equations
    Frm-fst-β : {A : Set} {B : A → Set}
      → {n : ℕ} (f : Frm A n) (f↓ : Frm↓ A B f)
      → Frm-fst (Frm-pr f f↓) ↦ f
    {-# REWRITE Frm-fst-β #-}

    Frm-snd-β : {A : Set} {B : A → Set}
      → {n : ℕ} (f : Frm A n) (f↓ : Frm↓ A B f)
      → Frm-snd (Frm-pr f f↓) ↦ f↓
    {-# REWRITE Frm-snd-β #-}
    
    Frm-pr-β : {A : Set} {B : A → Set}
      → {n : ℕ} (f : Frm (Σ A B) n)
      → Frm-pr (Frm-fst f) (Frm-snd f) ↦ f
    {-# REWRITE Frm-pr-β #-}

    -- Tree equations
    Tree-fst-β : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm A n} {f↓ : Frm↓ A B f}
      → (σ : Tree A f) (σ↓ : Tree↓ A B f↓ σ)
      → Tree-fst (Tree-pr σ σ↓) ↦ σ
    {-# REWRITE Tree-fst-β #-}
      
    Tree-snd-β : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm A n} {f↓ : Frm↓ A B f}
      → (σ : Tree A f) (σ↓ : Tree↓ A B f↓ σ)
      → Tree-snd (Tree-pr σ σ↓) ↦ σ↓
    {-# REWRITE Tree-snd-β #-}
      
    Tree-pr-β : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm (Σ A B) n}
      → (σ : Tree (Σ A B) f)
      → Tree-pr (Tree-fst σ) (Tree-snd σ) ↦ σ
    {-# REWRITE Tree-pr-β #-}

    -- Again, I'm not so sure about the orientation here ...
    Tree-pr-η : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm A n} {f↓ : Frm↓ A B f}
      → (τ : Cell A f) (τ↓ : Cell↓ A B f↓ τ)
      → Tree-pr (η f τ) (η↓ f↓ τ↓) ↦ η (Frm-pr f f↓) (Cell-pr τ τ↓)
    {-# REWRITE Tree-pr-η #-}

    Tree-fst-η : {A : Set} {B : A → Set}
      → {n : ℕ} (f : Frm (Σ A B) n) (τ : Cell (Σ A B) f)
      → Tree-fst (η f τ) ↦ η (Frm-fst f) (Cell-fst τ)
    {-# REWRITE Tree-fst-η #-}

    Tree-pr-μ : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm A n} {σ : Tree A f}
      → {δ : (p : Pos σ) → Tree A (Typ σ p)}
      → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ)
      → (δ↓ : (p : Pos σ) → Tree↓ A B (Typ↓ σ↓ p) (δ p))
      → Tree-pr (μ σ δ) (μ↓ σ↓ δ↓) ↦ μ (Tree-pr σ σ↓) (λ p → Tree-pr (δ p) (δ↓ p))
    {-# REWRITE Tree-pr-μ #-}

    Tree-fst-μ : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm (Σ A B) n}
      → (σ : Tree (Σ A B) f)
      → (δ : (p : Pos σ) → Tree (Σ A B) (Typ σ p))
      → Tree-fst (μ σ δ) ↦ μ (Tree-fst σ) (λ p → Tree-fst (δ p)) 
    {-# REWRITE Tree-fst-μ #-}

  Tree-pr (ob τ) (ob↓ τ↓) = ob (Cell-pr τ τ↓)
  Tree-pr (lf f τ) (lf↓ f↓ τ↓) = lf (Frm-pr f f↓) (Cell-pr τ τ↓)
  Tree-pr (nd f σ τ θ δ ε) (nd↓ {f↓ = f↓} σ↓ τ↓ θ↓ δ↓ ε↓) =
    nd (Frm-pr f f↓) (Tree-pr σ σ↓) (Cell-pr τ τ↓) (Cell-pr θ θ↓)
       (λ p → Tree-pr (δ p) (δ↓ p))
       (λ p → Tree-pr (ε p) (ε↓ p))

  Tree-fst (ob τ) = ob (Cell-fst τ)
  Tree-fst (lf f α) = lf (Frm-fst f) (Cell-fst α)
  Tree-fst (nd f σ τ α δ ε) = nd (Frm-fst f) (Tree-fst σ) (Cell-fst τ) (Cell-fst α)
    (λ p → Tree-fst (δ p)) 
    (λ p → Tree-fst (ε p)) 

  Tree-snd σ = {!!}



