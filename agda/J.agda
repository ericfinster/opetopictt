{-# OPTIONS --without-K --rewriting #-}

open import Base
open import Opetopes
open import OpetopicType
open import OpetopicTypeOver
open import Cell
open import CellOverCell

module J where

  is-contr : Set → Set
  is-contr A = Σ A (λ a₀ → (a₁ : A) → Cell A (□ a₀ ▹ a₁))

  postulate

    refl-is-unique : (A : Set) (a₀ : A)
      → (a₁ : A) (p : Cell A (□ a₀ ▹ a₁))
      → Cell (Σ A (λ a → Cell A (□ a₀ ▹ a))) (□ a₀ , Cell-refl a₀ ○ ▹ a₁ , p)

    -- Since we already *have* a canonical choice in dimension 0, it
    -- is more natural to state the previous axiom asseting that the
    -- reflexivity cell is unique, as opposed to singletons-contr,
    -- where the result would be opaque ...
    
    -- singletons-contr : (A : Set) (a₀ : A)
    --   → is-contr (Σ A (λ a₁ → Cell A (□ a₀ ▹ a₁)))

    types-are-kan : (A : Set)
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm A o} (σ : Tree A f t)
      → is-contr (Σ (Cell A f) (λ τ → Cell A (f ∥ σ ▹ τ)))

    transport-is-unique : (A : Set) (B : A → Set)
      → {a₀ : A} {a₁ : A} (p : Cell A (□ a₀ ▹ a₁))
      → (b₀ : B a₀)
      → is-contr (Σ (B a₁) (λ b₁ → Cell↓ A B (■ b₀ ▸ b₁) p))

    fibrations-are-kan : (A : Set) (B : A → Set)
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm A o} {σ : Tree A f t}
      → {τ : Cell A f} {θ : Cell A (f ∥ σ ▹ τ)}
      → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ)
      → is-contr (Σ (Cell↓ A B f↓ τ) (λ τ↓ → Cell↓ A B (f↓ ∥ σ↓ ▸ τ↓) θ))

  J : (A : Set) (a₀ : A)
    → (P : Σ A (λ a₁ → Cell A (□ a₀ ▹ a₁)) → Set)
    → (d : P (a₀ , Cell-refl a₀ ○))
    → (a₁ : A) (p : Cell A (□ a₀ ▹ a₁)) → P (a₁ , p)
  J A a₀ P d a₁ p = fst (fst (transport-is-unique (Σ A (λ a₁ → Cell A (□ a₀ ▹ a₁))) P (refl-is-unique A a₀ a₁ p) d))

