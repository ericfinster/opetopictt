{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module LocalOpetopicType where

  postulate

    𝕆 : Type₀
    Frm : (A : 𝕆) → ℕ → Type₀

  data Tree (A : 𝕆) : {n : ℕ} (f : Frm A n) → Type₀

  postulate

    Cell : (A : 𝕆) {n : ℕ} (f : Frm A n) → Type₀
    _∥_▸_ : {A : 𝕆} {n : ℕ} (f : Frm A n) (σ : Tree A f) (τ : Cell A f) → Frm A (S n)
    
    Pos : {A : 𝕆} {n : ℕ} {f : Frm A n} → Tree A f → Type₀

  Typ : {A : 𝕆} {n : ℕ} {f : Frm A n}
    → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
    → (p : Pos σ) → Frm A n
  Typ = {!!}

  Inh : {A : 𝕆} {n : ℕ} {f : Frm A n}
    → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
    → (p : Pos σ) → Cell A (Typ σ τ ρ p)
  Inh = {!!}

  η : {A : 𝕆} {n : ℕ} {f : Frm A n} → Cell A f → Tree A f
  η = {!!}
  
  μ : {A : 𝕆} {n : ℕ} {f : Frm A n}
    → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
    → (κ : (p : Pos σ) → Tree A (Typ σ τ ρ p))
    → Tree A f
  μ = {!!}

  data Tree (A : 𝕆) where
    lf : {n : ℕ} (f : Frm A n) (α : Cell A f)
      → Tree A (f ∥ η α ▸ α)
    nd : {n : ℕ} {f : Frm A n} 
      → (σ : Tree A f) (τ : Cell A f)  (α : Cell A (f ∥ σ ▸ τ))
      → (δ : (p : Pos σ) → Tree A (Typ σ τ (η α) p))
      → (ε : (p : Pos σ) → Tree A (Typ σ τ (η α) p ∥ δ p ▸ Inh σ τ (η α) p))
      → Tree A (f ∥ μ σ τ (η α) δ ▸ τ)

