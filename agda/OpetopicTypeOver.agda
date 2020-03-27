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

  Typ↓ : {A : Set} {B : A → Set}
    → {n : ℕ} {f : Frm A n} {f↓ : Frm↓ A B f}
    → {σ : Tree A f} (σ↓ : Tree↓ A B f↓ σ)
    → (p : Pos σ)
    → Frm↓ A B (Typ σ p)

  Inh↓ : {A : Set} {B : A → Set}
    → {n : ℕ} {f : Frm A n} {f↓ : Frm↓ A B f}
    → {σ : Tree A f} (σ↓ : Tree↓ A B f↓ σ)
    → (p : Pos σ) 
    → Cell↓ A B (Typ↓ σ↓ p) (Inh σ p)

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
    → (δ↓ : (p : Pos σ) → Tree↓ A B (Typ↓ σ↓ p) (δ p))
    → Tree↓ A B f↓ (μ σ δ)

  γ↓ : {A : Set} {B : A → Set}
    → {n : ℕ} {f : Frm A n}
    → {σ : Tree A f} {τ : Cell A f} {ρ : Tree A (f ∣ σ ▸ τ)}
    → {ϕ : (p : Pos σ) → Tree A (Typ σ p)}
    → {ψ : (p : Pos σ) → Tree A (Typ σ p ∣ ϕ p ▸ Inh σ p)}
    → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ)
    → (τ↓ : Cell↓ A B f↓ τ) (ρ↓ : Tree↓ A B (f↓ ∥ σ↓ ▸ τ↓) ρ)
    → (ϕ↓ : (p : Pos σ) → Tree↓ A B (Typ↓ σ↓ p) (ϕ p))
    → (ψ↓ : (p : Pos σ) → Tree↓ A B (Typ↓ σ↓ p ∥ ϕ↓ p ▸ Inh↓ σ↓ p) (ψ p))
    → Tree↓ A B (f↓ ∥ μ↓ σ↓ ϕ↓ ▸ τ↓) (γ σ τ ρ ϕ ψ)

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
      → (δ↓ : (p : Pos σ) → Tree↓ A B (Typ↓ σ↓ p) (δ p))
      → (ε↓ : (p : Pos σ) → Tree↓ A B (Typ↓ σ↓ p ∥ δ↓ p ▸ Inh↓ σ↓ p) (ε p))
      → Tree↓ A B (f↓ ∥ μ↓ σ↓ δ↓ ▸ τ↓) (nd f σ τ θ δ ε)

  Typ↓ (ob↓ τ↓) unit = ■
  Typ↓ (nd↓ σ↓ τ↓ θ↓ δ↓ ε↓) (inl unit) = _ ∥ σ↓ ▸ τ↓
  Typ↓ (nd↓ σ↓ τ↓ θ↓ δ↓ ε↓) (inr (p , q)) = Typ↓ (ε↓ p) q

  Inh↓ (ob↓ τ↓) unit = τ↓
  Inh↓ (nd↓ σ↓ τ↓ θ↓ δ↓ ε↓) (inl unit) = θ↓
  Inh↓ (nd↓ σ↓ τ↓ θ↓ δ↓ ε↓) (inr (p , q)) = Inh↓ (ε↓ p) q

  postulate

    -- Cell laws
    -- Cell↓-■ : {A : Set} {B : A → Set}
    --   → Cell↓ A B ■ ↦ B
    -- {-# REWRITE Cell↓-■ #-}
    
    -- Typ/Inh laws
    η↓-pos-typ : {A : Set} {B : A → Set} {n : ℕ}
      → {f : Frm A n} {τ : Cell A f}
      → (f↓ : Frm↓ A B f) (τ↓ : Cell↓ A B f↓ τ)
      → (p : Pos (η f τ))
      → Typ↓ (η↓ f↓ τ↓) p ↦ f↓
    {-# REWRITE η↓-pos-typ #-}

    η↓-pos-inh : {A : Set} {B : A → Set} {n : ℕ}
      → {f : Frm A n} {τ : Cell A f}
      → (f↓ : Frm↓ A B f) (τ↓ : Cell↓ A B f↓ τ)
      → (p : Pos (η f τ))
      → Inh↓ (η↓ f↓ τ↓) p ↦ τ↓
    {-# REWRITE η↓-pos-inh #-}

    μ↓-pos-typ : {A : Set} {B : A → Set} {n : ℕ}
      → {f : Frm A n} {σ : Tree A f}
      → {δ : (p : Pos σ) → Tree A (Typ σ p)}
      → (f↓ : Frm↓ A B f) (σ↓ : Tree↓ A B f↓ σ)
      → (δ↓ : (p : Pos σ) → Tree↓ A B (Typ↓ σ↓ p) (δ p))
      → (p : Pos (μ σ δ))
      → Typ↓ (μ↓ σ↓ δ↓) p ↦ Typ↓ (δ↓ (μ-pos-fst σ δ p)) (μ-pos-snd σ δ p)
    {-# REWRITE μ↓-pos-typ #-}

    μ↓-pos-inh : {A : Set} {B : A → Set} {n : ℕ}
      → {f : Frm A n} {σ : Tree A f}
      → {δ : (p : Pos σ) → Tree A (Typ σ p)}
      → (f↓ : Frm↓ A B f) (σ↓ : Tree↓ A B f↓ σ)
      → (δ↓ : (p : Pos σ) → Tree↓ A B (Typ↓ σ↓ p) (δ p))
      → (p : Pos (μ σ δ))
      → Inh↓ (μ↓ σ↓ δ↓) p ↦ Inh↓ (δ↓ (μ-pos-fst σ δ p)) (μ-pos-snd σ δ p)
    {-# REWRITE μ↓-pos-inh #-}

    -- μ↓ laws
    μ↓-unit-r : {A : Set} {B : A → Set} {n : ℕ}
      → {f : Frm A n} {σ : Tree A f}
      → (f↓ : Frm↓ A B f) (σ↓ : Tree↓ A B f↓ σ)
      → μ↓ σ↓ (λ p → η↓ (Typ↓ σ↓ p) (Inh↓ σ↓ p)) ↦ σ↓
    {-# REWRITE μ↓-unit-r #-}

    μ↓-unit-l : {A : Set} {B : A → Set} {n : ℕ}
      → {f : Frm A n} {τ : Cell A f}
      → {δ : (p : Pos (η f τ)) → Tree A (Typ (η f τ) p)}
      → (f↓ : Frm↓ A B f) (τ↓ : Cell↓ A B f↓ τ)
      → (δ↓ : (p : Pos (η f τ)) → Tree↓ A B (Typ↓ (η↓ f↓ τ↓) p) (δ p))
      → μ↓ (η↓ f↓ τ↓) δ↓ ↦ δ↓ (η-pos f τ)
    {-# REWRITE μ↓-unit-l #-}
    
    μ↓-assoc : {A : Set} {B : A → Set} {n : ℕ}
      → {f : Frm A n} {σ : Tree A f}
      → {δ : (p : Pos σ) → Tree A (Typ σ p)}
      → {ε : (p : Pos (μ σ δ)) → Tree A (Typ (μ σ δ) p)}
      → (f↓ : Frm↓ A B f) (σ↓ : Tree↓ A B f↓ σ)
      → (δ↓ : (p : Pos σ) → Tree↓ A B (Typ↓ σ↓ p) (δ p))
      → (ε↓ : (p : Pos (μ σ δ)) → Tree↓ A B (Typ↓ (μ↓ σ↓ δ↓) p) (ε p))
      → μ↓ (μ↓ σ↓ δ↓) ε↓ ↦ μ↓ σ↓ (λ p → μ↓ (δ↓ p) (λ q →  ε↓ (μ-pos σ δ p q)))
    {-# REWRITE μ↓-assoc #-}

  η↓ {f = ●} ■ τ↓ = ob↓ τ↓
  η↓ {f = f ∣ σ ▸ τ} {τ = θ} (f↓ ∥ σ↓ ▸ τ↓) θ↓ = 
    let η↓-dec p = η↓ (Typ↓ σ↓ p) (Inh↓ σ↓ p)
        lf↓-dec p = lf↓ (Typ↓ σ↓ p) (Inh↓ σ↓ p)
    in nd↓ σ↓ τ↓ θ↓ η↓-dec lf↓-dec 

  μ↓ (ob↓ τ↓) κ↓ = κ↓ unit
  μ↓ (lf↓ f↓ τ↓) κ↓ = lf↓ f↓ τ↓
  μ↓ (nd↓ σ↓ τ↓ θ↓ δ↓ ε↓) κ↓ =
    let w↓ = κ↓ (inl unit)
        κ↓↑ p q = κ↓ (inr (p , q))
        ψ↓ p = μ↓ (ε↓ p) (κ↓↑ p)
    in γ↓ σ↓ τ↓ w↓ δ↓ ψ↓

  γ↓ {f = f} {τ = τ} .(η↓ _ τ↓) τ↓ (lf↓ _ .τ↓) ϕ↓ ψ↓ = ψ↓ (η-pos f τ)
  γ↓ {ρ = nd f σ τ θ δ ε} .(μ↓ σ↓ δ↓) τ↓ (nd↓ σ↓ .τ↓ θ↓ δ↓ ε↓) ϕ↓ ψ↓ =
    let ϕ↓↑ p q = ϕ↓ (μ-pos σ δ p q)
        ψ↓↑ p q = ψ↓ (μ-pos σ δ p q)
        δ↓↑ p = μ↓ (δ↓ p) (ϕ↓↑ p)
        ε↓↑ p = γ↓ (δ↓ p) (Inh↓ σ↓ p) (ε↓ p) (ϕ↓↑ p) (ψ↓↑ p)
    in nd↓ σ↓ τ↓ θ↓ δ↓↑ ε↓↑



