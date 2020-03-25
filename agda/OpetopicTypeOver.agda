{-# OPTIONS --without-K --rewriting #-}

open import Base
open import OpetopicType

module OpetopicTypeOver where

  data Frm↓ (A : Set) (B : A → Set) :
    {n : ℕ} (f : Frm A n) → Set
    
  data Tree↓ (A : Set) (B : A → Set) :
      {n : ℕ} {f : Frm A n}
    → (f↓ : Frm↓ A B f) (σ : Tree A f) → Set

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

  infixl 30 _∥_▸_

  data Frm↓ A B where
    ■ : Frm↓ A B ●
    _∥_▸_ : {n : ℕ} {f : Frm A n}
      → (f↓ : Frm↓ A B f)
      → {σ : Tree A f} (σ↓ : Tree↓ A B f↓ σ)
      → {τ : Cell A f} (τ↓ : Cell↓ A B f↓ τ)
      → Frm↓ A B (f ∣ σ ▸ τ)

  η↓ : {A : Set} {B : A → Set}
    → {n : ℕ} {f : Frm A n} {τ : Cell A f}
    → (f↓ : Frm↓ A B f)(τ↓ : Cell↓ A B f↓ τ)
    → Tree↓ A B f↓ (η f τ)

  μ↓ : {A : Set} {B : A → Set}
    → {n : ℕ} {f : Frm A n} {σ : Tree A f}
    → {δ : (p : Pos σ) → Tree A (Typ σ p)}
    → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ)
    → (δ↓ : {p : Pos σ} (p↓ : Pos↓ σ↓ p) → Tree↓ A B (Typ↓ σ↓ p↓) (δ p))
    → Tree↓ A B f↓ (μ σ δ)

  data Tree↓ A B where
  
    ob↓ : {τ : Cell A ●} (τ↓ : Cell↓ A B ■ τ)
      → Tree↓ A B ■ (ob τ)

    lf↓ : {n : ℕ} {f : Frm A n} {τ : Cell A f}
      → (f↓ : Frm↓ A B f) (τ↓ : Cell↓ A B f↓ τ)
      → Tree↓ A B (f↓ ∥ η↓ f↓ τ↓ ▸ τ↓) (lf f τ)

    nd↓ : {n : ℕ} {f : Frm A n}
      → {σ : Tree A f} {τ : Cell A f} {θ : Cell A (f ∣ σ ▸ τ)}
      → {δ : (p : Pos σ) → Tree A (Typ σ p)}
      → {ε : (p : Pos σ) → Tree A (Typ σ p ∣ δ p ▸ Inh σ p)}
      → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ) (τ↓ : Cell↓ A B f↓ τ)
      → (θ↓ : Cell↓ A B (f↓ ∥ σ↓ ▸ τ↓) θ)
      → (δ↓ : {p : Pos σ} (p↓ : Pos↓ σ↓ p) → Tree↓ A B (Typ↓ σ↓ p↓) (δ p))
      → (ε↓ : {p : Pos σ} (p↓ : Pos↓ σ↓ p) → Tree↓ A B (Typ↓ σ↓ p↓ ∥ δ↓ p↓ ▸ Inh↓ σ↓ p↓) (ε p))
      → Tree↓ A B (f↓ ∥ μ↓ σ↓ δ↓ ▸ τ↓) (nd f σ τ θ δ ε)

  Pos↓ = {!!}
  Typ↓ = {!!}
  Inh↓ = {!!}

  η↓ = {!!}
  μ↓ = {!!}
