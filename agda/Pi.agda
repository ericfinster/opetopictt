{-# OPTIONS --without-K --rewriting #-}

open import Base
open import Opetopes
open import OpetopicType
open import OpetopicTypeOver

module Pi where

  -- Non-dependent Π

  Frm-ev : {A : Set} {B : A → Set}
    → {n : ℕ} {o : 𝕆 n}
    → (f : Frm (Π A B) o)
    → (af : Frm A o)
    → Frm↓ A B af

  Tree-ev : {A : Set} {B : A → Set}
    → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → {f : Frm (Π A B) o} (σ : Tree (Π A B) f t)
    → {af : Frm A o} (aσ : Tree A af t)
    → Tree↓ A B (Frm-ev f af) aσ

  postulate

    Cell-Π : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n}
      → {f : Frm (Π A B) o}
      → Cell (Π A B) f ↦ ((af : Frm A o) (a : Cell A af) → Cell↓ A B (Frm-ev f af) a)
    {-# REWRITE Cell-Π #-}

    Tree-ev-typ : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm (Π A B) o} (σ : Tree (Π A B) f t)
      → {af : Frm A o} (aσ : Tree A af t)
      → (p : Pos t)
      → Typ↓ (Tree-ev σ aσ) p ↦ Frm-ev (Typ σ p) (Typ aσ p)
    {-# REWRITE Tree-ev-typ #-}

    Tree-ev-inh : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm (Π A B) o} (σ : Tree (Π A B) f t)
      → {af : Frm A o} (aσ : Tree A af t)
      → (p : Pos t)
      → Inh↓ (Tree-ev σ aσ) p ↦ Inh σ p (Typ aσ p) (Inh aσ p)
    {-# REWRITE Tree-ev-inh #-}

    Tree-ev-η : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n} 
      → {f : Frm (Π A B) o} (τ : Cell (Π A B) f)
      → {af : Frm A o} (aτ : Cell A af)
      → Tree-ev (η f τ) (η af aτ) ↦ η↓ (Frm-ev f af) (τ af aτ) 
    {-# REWRITE Tree-ev-η #-}

    Tree-ev-μ : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
      → {f : Frm (Π A B) o} (σ : Tree (Π A B) f t)
      → (δ : (p : Pos t) → Tree (Π A B) (Typ σ p) (δₒ p))
      → {af : Frm A o} (aσ : Tree A af t)
      → (aδ : (p : Pos t) → Tree A (Typ aσ p) (δₒ p))
      → Tree-ev (μ σ δ) (μ aσ aδ) ↦ μ↓ (Tree-ev σ aσ) (λ p → Tree-ev (δ p) (aδ p))
    {-# REWRITE Tree-ev-μ #-}

  Frm-ev (□ s₀ ▹ s₁) (□ a₀ ▹ a₁) = ■ s₀ a₀ ▸ s₁ a₁
  Frm-ev (f ∥ σ ▹ τ) (af ∥ aσ ▹ aτ) =
    Frm-ev f af ∥ Tree-ev σ aσ ▸ τ af aτ

  Tree-ev (nil s) (nil a) = nil↓ (s a)
  Tree-ev (cns sρ sσ) (cns aρ aσ) = cns↓ (sρ _ aρ) (Tree-ev sσ aσ)
  Tree-ev (lf sf sτ) (lf af aτ) = lf↓ (Frm-ev sf af) (sτ af aτ)
  Tree-ev (nd sσ sτ sθ sδ sε) (nd {f = af} aσ aτ aθ aδ aε) =
    nd↓ (Tree-ev sσ aσ) (sτ af aτ) (sθ (af ∥ aσ ▹ aτ) aθ)
        (λ p → Tree-ev (sδ p) (aδ p))
        (λ p → Tree-ev (sε p) (aε p))
