{-# OPTIONS --without-K --rewriting #-}

open import Base
open import OpetopicType
open import OpetopicTypeOver

module Sigma where

  -- Rules for non-dependent Σ

  Frm-fst : {A : Set} {B : A → Set}
    → {n : ℕ} (f : Frm (Σ A B) n)
    → Frm A n

  Frm-snd : {A : Set} {B : A → Set}
    → {n : ℕ} (f : Frm (Σ A B) n)
    → Frm↓ A B (Frm-fst f)

  Tree-fst : {A : Set} {B : A → Set}
    → {n : ℕ} {f : Frm (Σ A B) n}
    → Tree (Σ A B) f → Tree A (Frm-fst f)

  Tree-snd : {A : Set} {B : A → Set}
    → {n : ℕ} {f : Frm (Σ A B) n}
    → (σ : Tree (Σ A B) f)
    → Tree↓ A B (Frm-snd f) (Tree-fst σ)
    
  postulate

    Cell-fst : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm (Σ A B) n}
      → Cell (Σ A B) f → Cell A (Frm-fst f)

    Cell-snd : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm (Σ A B) n}
      → (τ : Cell (Σ A B) f)
      → Cell↓ A B (Frm-snd f) (Cell-fst τ)

  Frm-fst ● = ●
  Frm-fst (f ∣ σ ▸ τ) = Frm-fst f ∣ Tree-fst σ ▸ Cell-fst τ
  
  Frm-snd ● = ■
  Frm-snd (f ∣ σ ▸ τ) = Frm-snd f ∥ Tree-snd σ ▸ Cell-snd τ

  postulate

    η-Tree-fst : {A : Set} {B : A → Set}
      → {n : ℕ} (f : Frm (Σ A B) n) (τ : Cell (Σ A B) f)
      → Tree-fst (η f τ) ↦ η (Frm-fst f) (Cell-fst τ)
    {-# REWRITE η-Tree-fst #-}

    μ-Tree-fst : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm (Σ A B) n}
      → (σ : Tree (Σ A B) f)
      → (δ : (p : Pos σ) → Tree (Σ A B) (Typ σ p))
      → Tree-fst (μ σ δ) ↦ μ (Tree-fst σ) (λ p → {!!})

  -- Oh.  I see.  We need to know that the positions of
  -- a projected tree are the same as positions in the
  -- original.  And this makes sense I guess: the extra
  -- data of the position in the tree over is irrelevant.

  Tree-fst (ob τ) = ob (Cell-fst τ)
  Tree-fst (lf f α) = lf (Frm-fst f) (Cell-fst α)
  Tree-fst (nd f σ τ α δ ε) = {!nd (Frm-fst f) (Tree-fst σ) (Cell-fst τ) (Cell-fst α)!}

  Tree-snd σ = {!!}

  -- postulate

  --   Σ-Frm : {A : Set} {B : A → Set} {n : ℕ}
  --     → Frm (Σ A B) n ↦ Σ (Frm A n) (λ f → Frm↓ A B f)

  -- Hmm.  Yikes. I cannot rewrite a data type name.  So
  -- I will not be able to make Frames, Cells and Trees
  -- compute definitionally.  But if I equip the cells with
  -- the usual constructors, maybe this will be enough ...

