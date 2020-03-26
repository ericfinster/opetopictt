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

  postulate
  
    η↓ : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm A n} {τ : Cell A f}
      → (f↓ : Frm↓ A B f)(τ↓ : Cell↓ A B f↓ τ)
      → Tree↓ A B f↓ (η f τ)

    η-pos↓ : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm A n} {τ : Cell A f}
      → (f↓ : Frm↓ A B f)(τ↓ : Cell↓ A B f↓ τ)
      → Pos↓ (η↓ f↓ τ↓) (η-pos f τ)

    η-pos-elim↓ : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm A n} {τ : Cell A f}
      → (f↓ : Frm↓ A B f)(τ↓ : Cell↓ A B f↓ τ)
      → (X : {p : Pos (η f τ)} (p↓ : Pos↓ (η↓ f↓ τ↓) p) → Set)
      → (η-pos↓* : X (η-pos↓ f↓ τ↓))
      → {p : Pos (η f τ)} (p↓ : Pos↓ (η↓ f↓ τ↓) p) → X p↓

    μ↓ : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm A n} {σ : Tree A f}
      → {δ : (p : Pos σ) → Tree A (Typ σ p)}
      → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ)
      → (δ↓ : {p : Pos σ} (p↓ : Pos↓ σ↓ p) → Tree↓ A B (Typ↓ σ↓ p↓) (δ p))
      → Tree↓ A B f↓ (μ σ δ)

    μ-pos↓ : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm A n} {σ : Tree A f}
      → {δ : (p : Pos σ) → Tree A (Typ σ p)}
      → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ)
      → (δ↓ : {p : Pos σ} (p↓ : Pos↓ σ↓ p) → Tree↓ A B (Typ↓ σ↓ p↓) (δ p))
      → {p : Pos σ} {q : Pos (δ p)}
      → (p↓ : Pos↓ σ↓ p) (q↓ : Pos↓ (δ↓ p↓) q)
      → Pos↓ (μ↓ σ↓ δ↓) (μ-pos σ δ p q)

    μ-pos-fst↓ : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm A n} {σ : Tree A f}
      → {δ : (p : Pos σ) → Tree A (Typ σ p)}
      → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ)
      → (δ↓ : {p : Pos σ} (p↓ : Pos↓ σ↓ p) → Tree↓ A B (Typ↓ σ↓ p↓) (δ p))
      → {p : Pos (μ σ δ)} (p↓ : Pos↓ (μ↓ σ↓ δ↓) p)
      → Pos↓ σ↓ (μ-pos-fst σ δ p)

    μ-pos-snd↓ : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm A n} {σ : Tree A f}
      → {δ : (p : Pos σ) → Tree A (Typ σ p)}
      → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ)
      → (δ↓ : {p : Pos σ} (p↓ : Pos↓ σ↓ p) → Tree↓ A B (Typ↓ σ↓ p↓) (δ p))
      → {p : Pos (μ σ δ)} (p↓ : Pos↓ (μ↓ σ↓ δ↓) p)
      → Pos↓ (δ↓ (μ-pos-fst↓ σ↓ δ↓ p↓)) (μ-pos-snd σ δ p) 

    γ↓ : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm A n}
      → {σ : Tree A f} {τ : Cell A f} {ρ : Tree A (f ∣ σ ▸ τ)}
      → {ϕ : (p : Pos σ) → Tree A (Typ σ p)}
      → {ψ : (p : Pos σ) → Tree A (Typ σ p ∣ ϕ p ▸ Inh σ p)}
      → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ)
      → (τ↓ : Cell↓ A B f↓ τ) (ρ↓ : Tree↓ A B (f↓ ∥ σ↓ ▸ τ↓) ρ)
      → (ϕ↓ : {p : Pos σ} (p↓ : Pos↓ σ↓ p) → Tree↓ A B (Typ↓ σ↓ p↓) (ϕ p))
      → (ψ↓ : {p : Pos σ} (p↓ : Pos↓ σ↓ p) → Tree↓ A B (Typ↓ σ↓ p↓ ∥ ϕ↓ p↓ ▸ Inh↓ σ↓ p↓) (ψ p))
      → Tree↓ A B (f↓ ∥ μ↓ σ↓ ϕ↓ ▸ τ↓) (γ σ τ ρ ϕ ψ)

    γ-pos-inl↓ : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm A n}
      → {σ : Tree A f} {τ : Cell A f} {ρ : Tree A (f ∣ σ ▸ τ)}
      → {ϕ : (p : Pos σ) → Tree A (Typ σ p)}
      → {ψ : (p : Pos σ) → Tree A (Typ σ p ∣ ϕ p ▸ Inh σ p)}
      → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ)
      → (τ↓ : Cell↓ A B f↓ τ) (ρ↓ : Tree↓ A B (f↓ ∥ σ↓ ▸ τ↓) ρ)
      → (ϕ↓ : {p : Pos σ} (p↓ : Pos↓ σ↓ p) → Tree↓ A B (Typ↓ σ↓ p↓) (ϕ p))
      → (ψ↓ : {p : Pos σ} (p↓ : Pos↓ σ↓ p) → Tree↓ A B (Typ↓ σ↓ p↓ ∥ ϕ↓ p↓ ▸ Inh↓ σ↓ p↓) (ψ p))
      → {p : Pos ρ} (p↓ : Pos↓ ρ↓ p)
      → Pos↓ (γ↓ σ↓ τ↓ ρ↓ ϕ↓ ψ↓) (γ-pos-inl σ τ ρ ϕ ψ p)

    γ-pos-inr↓ : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm A n}
      → {σ : Tree A f} {τ : Cell A f} {ρ : Tree A (f ∣ σ ▸ τ)}
      → {ϕ : (p : Pos σ) → Tree A (Typ σ p)}
      → {ψ : (p : Pos σ) → Tree A (Typ σ p ∣ ϕ p ▸ Inh σ p)}
      → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ)
      → (τ↓ : Cell↓ A B f↓ τ) (ρ↓ : Tree↓ A B (f↓ ∥ σ↓ ▸ τ↓) ρ)
      → (ϕ↓ : {p : Pos σ} (p↓ : Pos↓ σ↓ p) → Tree↓ A B (Typ↓ σ↓ p↓) (ϕ p))
      → (ψ↓ : {p : Pos σ} (p↓ : Pos↓ σ↓ p) → Tree↓ A B (Typ↓ σ↓ p↓ ∥ ϕ↓ p↓ ▸ Inh↓ σ↓ p↓) (ψ p))
      → {p : Pos σ} {q : Pos (ψ p)}
      → (p↓ : Pos↓ σ↓ p) (q↓ : Pos↓ (ψ↓ p↓) q)
      → Pos↓ (γ↓ σ↓ τ↓ ρ↓ ϕ↓ ψ↓) (γ-pos-inr σ τ ρ ϕ ψ p q)

    γ-pos-elim↓ : {A : Set} {B : A → Set}
      → {n : ℕ} {f : Frm A n}
      → {σ : Tree A f} {τ : Cell A f} {ρ : Tree A (f ∣ σ ▸ τ)}
      → {ϕ : (p : Pos σ) → Tree A (Typ σ p)}
      → {ψ : (p : Pos σ) → Tree A (Typ σ p ∣ ϕ p ▸ Inh σ p)}
      → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ)
      → (τ↓ : Cell↓ A B f↓ τ) (ρ↓ : Tree↓ A B (f↓ ∥ σ↓ ▸ τ↓) ρ)
      → (ϕ↓ : {p : Pos σ} (p↓ : Pos↓ σ↓ p) → Tree↓ A B (Typ↓ σ↓ p↓) (ϕ p))
      → (ψ↓ : {p : Pos σ} (p↓ : Pos↓ σ↓ p) → Tree↓ A B (Typ↓ σ↓ p↓ ∥ ϕ↓ p↓ ▸ Inh↓ σ↓ p↓) (ψ p))
      → (X : {p : Pos (γ σ τ ρ ϕ ψ)} (p↓ : Pos↓ (γ↓ σ↓ τ↓ ρ↓ ϕ↓ ψ↓) p) → Set)
      → (inl* : {p : Pos ρ} (p↓ : Pos↓ ρ↓ p) → X (γ-pos-inl↓ σ↓ τ↓ ρ↓ ϕ↓ ψ↓ p↓))
      → (inr* : {p : Pos σ} {q : Pos (ψ p)}
                (p↓ : Pos↓ σ↓ p) (q↓ : Pos↓ (ψ↓ p↓) q) → X (γ-pos-inr↓ σ↓ τ↓ ρ↓ ϕ↓ ψ↓ p↓ q↓))
      → {p : Pos (γ σ τ ρ ϕ ψ)} (p↓ : Pos↓ (γ↓ σ↓ τ↓ ρ↓ ϕ↓ ψ↓) p) → X p↓

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

  Pos↓ (ob↓ τ↓) unit = ⊤
  Pos↓ (lf↓ f↓ τ↓) ()
  Pos↓ (nd↓ σ↓ τ↓ θ↓ δ↓ ε↓) (inl unit) = ⊤
  Pos↓ (nd↓ σ↓ τ↓ θ↓ δ↓ ε↓) (inr (p , q)) =
    Σ (Pos↓ σ↓ p) (λ p↓ → Pos↓ (ε↓ p↓) q)

  Typ↓ (ob↓ τ↓) {unit} unit = ■
  Typ↓ (nd↓ σ↓ τ↓ θ↓ δ↓ ε↓) {inl unit} unit = _ ∥ σ↓ ▸ τ↓
  Typ↓ (nd↓ σ↓ τ↓ θ↓ δ↓ ε↓) {inr (p , q)} (p↓ , q↓) = Typ↓ (ε↓ p↓) q↓

  Inh↓ (ob↓ τ↓) {unit} unit = τ↓
  Inh↓ (nd↓ σ↓ τ↓ θ↓ δ↓ ε↓) {inl unit} unit = θ↓
  Inh↓ (nd↓ σ↓ τ↓ θ↓ δ↓ ε↓) {inr (p , q)} (p↓ , q↓) = Inh↓ (ε↓ p↓) q↓

  -- η↓ = {!!}
  -- η-pos↓ = {!!}
  -- η-pos-elim↓ = {!!}

  -- μ↓ = {!!}
  -- μ-pos↓ = {!!}
  -- μ-pos-fst↓ = {!!}
  -- μ-pos-snd↓ = {!!}

  -- γ↓ = {!!}
  -- γ-pos-inl↓ = {!!}
  -- γ-pos-inr↓ = {!!}
  -- γ-pos-elim↓ = {!!}

