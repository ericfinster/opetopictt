{-# OPTIONS --without-K --rewriting #-}

open import Base
open import OpetopicType

module OpetopicTypeOver where

  data Frm↓ (A : Set) (B : A → Set) : {n : ℕ} (f : Frm A n) → Set
  data Tree↓ (A : Set) (B : A → Set) : {n : ℕ} {f : Frm A n} (f↓ : Frm↓ A B f) (σ : Tree A f) → Set

  postulate

    Cell↓ : (A : Set) (B : A → Set)
      → {n : ℕ} {f : Frm A n}
      → (f↓ : Frm↓ A B f) (τ : Cell A f)
      → Set

  Pos↓ : {A : Set} {B : A → Set}
    → {n : ℕ} {f : Frm A n} {f↓ : Frm↓ A B f}
    → {σ : Tree A f} (σ↓ : Tree↓ A B f↓ σ)
    → Pos σ → Set

  Typ↓ : {A : Set} {B : A → Set}
    → {n : ℕ} {f : Frm A n} {f↓ : Frm↓ A B f}
    → {σ : Tree A f} (σ↓ : Tree↓ A B f↓ σ)
    → {p : Pos σ} (p↓ : Pos↓ σ↓ p)
    → Frm↓ A B (Typ σ p)

  Inh↓ : {A : Set} {B : A → Set}
    → {n : ℕ} {f : Frm A n} {f↓ : Frm↓ A B f}
    → {σ : Tree A f} (σ↓ : Tree↓ A B f↓ σ)
    → {p : Pos σ} (p↓ : Pos↓ σ↓ p)
    → Cell↓ A B (Typ↓ σ↓ p↓) (Inh σ p)

  data Frm↓ A B where
    ■ : Frm↓ A B ●
    _∥_▸_ : {n : ℕ} {f : Frm A n}
      → (f↓ : Frm↓ A B f)
      → {σ : Tree A f} (σ↓ : Tree↓ A B f↓ σ)
      → {τ : Cell A f} (τ↓ : Cell↓ A B f↓ τ)
      → Frm↓ A B (f ∣ σ ▸ τ)

  data Tree↓ A B where

  Pos↓ = {!!}
  Typ↓ = {!!}
  Inh↓ = {!!}
