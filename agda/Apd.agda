{-# OPTIONS --without-K --rewriting #-}

open import Base
open import OpetopicType
open import OpetopicTypeOver

module Apd where

  -- Primitive dependent application

  Frm-apd : {A : Set} {B : A → Set}
    → (b : (a : A) → B a)
    → {n : ℕ} (f : Frm A n)
    → Frm↓ A B f

  Tree-apd : {A : Set} {B : A → Set}
    → (b : (a : A) → B a)
    → {n : ℕ} {f : Frm A n}
    → (σ : Tree A f) → Tree↓ A B (Frm-apd b f) σ

  postulate

    Cell-apd : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm A n}
      → (b : (a : A) → B a)
      → (a : Cell A f) → Cell↓ A B (Frm-apd b f) a

    Tree-apd-η : {A : Set} {B : A → Set}
      → (b : (a : A) → B a)
      → {n : ℕ} {f : Frm A n} (τ : Cell A f)
      → Tree-apd b (η f τ) ↦ η↓ (Frm-apd b f) (Cell-apd b τ)
    {-# REWRITE Tree-apd-η #-}

  Frm-apd b ● = ■
  Frm-apd b (f ∣ σ ▸ τ) =
    Frm-apd b f ∥ Tree-apd b σ ▸ Cell-apd b τ
  
  Tree-apd b (ob τ) = ob↓ (Cell-apd b τ)
  Tree-apd b (lf f τ) = lf↓ (Frm-apd b f) (Cell-apd b τ)
  Tree-apd b (nd f σ τ θ δ ε) = {!!}

  -- Okay, and now same problem.  For the positions over, we've
  -- got a bit of a problem.....

  -- Right.  And so you are going to just say that it is structurally
  -- recursive and commutes appropriately with the opetopic signature.

  -- Then for each type construtor, you'll need to *implement* dependent
  -- application in terms of the appropriate intro/elim rules.
