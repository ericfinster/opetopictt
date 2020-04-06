{-# OPTIONS --without-K --rewriting #-}

open import Base

module OpetopicTypePrime where

  data Frm (A : Set) : ℕ → Set
  data Tree (A : Set) : {n : ℕ} (f : Frm A n) → Set
  
  postulate

    Cell : (A : Set) {n : ℕ} → Frm A n → Set
    
  Pos : {A : Set} {n : ℕ} {f : Frm A n} → Tree A f → Set

  Typ : {A : Set} {n : ℕ} {f : Frm A n}
    → (σ : Tree A f) (p : Pos σ)
    → Frm A n 

  Inh : {A : Set} {n : ℕ} {f : Frm A n}
    → (σ : Tree A f) (p : Pos σ)
    → Cell A (Typ σ p)

  infixl 30 _∣_▸_
  
  data Frm A where
    ●_▸_ : A → A → Frm A O 
    _∣_▸_ : {n : ℕ} (f : Frm A n)
      → (σ : Tree A f) (τ : Cell A f)
      → Frm A (S n)

  η : {A : Set} {n : ℕ} (f : Frm A n)
    → Cell A f → Tree A f

  -- η-pos : {A : Set} {n : ℕ}
  --   → (f : Frm A n) (τ : Cell A f)
  --   → Pos (η f τ)

  -- η-pos-elim : {A : Set} {n : ℕ}
  --   → (f : Frm A n) (τ : Cell A f)
  --   → (X : (p : Pos (η f τ)) → Set)
  --   → (η-pos* : X (η-pos f τ))
  --   → (p : Pos (η f τ)) → X p

  μ : {A : Set} {n : ℕ} {f : Frm A n}
    → (σ : Tree A f)
    → (δ : (p : Pos σ) → Tree A (Typ σ p))
    → Tree A f

  -- μ-pos : {A : Set} {n : ℕ}
  --   → {f : Frm A n} (σ : Tree A f)
  --   → (δ : (p : Pos σ) → Tree A (Typ σ p))
  --   → (p : Pos σ) (q : Pos (δ p))
  --   → Pos (μ σ δ)

  -- μ-pos-fst : {A : Set} {n : ℕ}
  --   → {f : Frm A n} (σ : Tree A f)
  --   → (δ : (p : Pos σ) → Tree A (Typ σ p))
  --   → Pos (μ σ δ) → Pos σ

  -- μ-pos-snd : {A : Set} {n : ℕ}
  --   → {f : Frm A n} (σ : Tree A f)
  --   → (δ : (p : Pos σ) → Tree A (Typ σ p))
  --   → (p : Pos (μ σ δ)) → Pos (δ (μ-pos-fst σ δ p))

  γ : {A : Set} {n : ℕ} {f : Frm A n}
    → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∣ σ ▸ τ))
    → (δ : (p : Pos σ) → Tree A (Typ σ p))
    → (ε : (p : Pos σ) → Tree A (Typ σ p ∣ δ p ▸ Inh σ p))
    → Tree A (f ∣ μ σ δ ▸ τ)

  -- γ-pos-inl : {A : Set} {n : ℕ} {f : Frm A n}
  --   → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∣ σ ▸ τ))
  --   → (ϕ : (p : Pos σ) → Tree A (Typ σ p))
  --   → (ψ : (p : Pos σ) → Tree A (Typ σ p ∣ ϕ p ▸ Inh σ p))
  --   → Pos ρ → Pos (γ σ τ ρ ϕ ψ)

  -- γ-pos-inr : {A : Set} {n : ℕ} {f : Frm A n}
  --   → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∣ σ ▸ τ))
  --   → (ϕ : (p : Pos σ) → Tree A (Typ σ p))
  --   → (ψ : (p : Pos σ) → Tree A (Typ σ p ∣ ϕ p ▸ Inh σ p))
  --   → (p : Pos σ) (q : Pos (ψ p))
  --   → Pos (γ σ τ ρ ϕ ψ)

  -- γ-pos-elim : {A : Set} {n : ℕ} {f : Frm A n}
  --   → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∣ σ ▸ τ))
  --   → (ϕ : (p : Pos σ) → Tree A (Typ σ p))
  --   → (ψ : (p : Pos σ) → Tree A (Typ σ p ∣ ϕ p ▸ Inh σ p))
  --   → (X : Pos (γ σ τ ρ ϕ ψ) → Set)
  --   → (inl* : (p : Pos ρ) → X (γ-pos-inl σ τ ρ ϕ ψ p))
  --   → (inr* : (p : Pos σ) (q : Pos (ψ p)) → X (γ-pos-inr σ τ ρ ϕ ψ p q))
  --   → (p : Pos (γ σ τ ρ ϕ ψ)) → X p

  data Tree A where

    nil : (a : A) → Tree A (● a ▸ a)
    cns : {a₀ a₁ a₂ : A} 
      → (ρ : Cell A (● a₀ ▸ a₁))
      → (θ : Tree A (● a₁ ▸ a₂))
      → Tree A (● a₀ ▸ a₂)
    
    lf : {n : ℕ} (f : Frm A n) (τ : Cell A f)
      → Tree A (f ∣ η f τ ▸ τ)
    nd : {n : ℕ} (f : Frm A n) 
      → (σ : Tree A f) (τ : Cell A f)  (θ : Cell A (f ∣ σ ▸ τ))
      → (δ : (p : Pos σ) → Tree A (Typ σ p))
      → (ε : (p : Pos σ) → Tree A (Typ σ p ∣ δ p ▸ Inh σ p))
      → Tree A (f ∣ μ σ δ ▸ τ)

  Pos (nil a) = ⊥
  Pos (cns ρ θ) = ⊤ ⊔ Pos θ
  Pos (lf f τ) = ⊥
  Pos (nd f σ τ θ δ ε) =
    ⊤ ⊔ Σ (Pos σ) (λ p → Pos (ε p))

  Typ (cns {a₀} {a₁} ρ σ) (inl unit) = ● a₀ ▸ a₁
  Typ (cns ρ σ) (inr p) = Typ σ p
  Typ (nd f σ τ θ δ ε) (inl unit) = f ∣ σ ▸ τ
  Typ (nd f σ τ θ δ ε) (inr (p , q)) = Typ (ε p) q

  Inh (cns ρ σ) (inl unit) = ρ
  Inh (cns ρ σ) (inr p) = Inh σ p
  Inh (nd f σ τ θ δ ε) (inl unit) = θ
  Inh (nd f σ τ θ δ ε) (inr (p , q)) = Inh (ε p) q

  postulate

    -- μ laws
    μ-unit-r : {A : Set} {n : ℕ}
      → (f : Frm A n) (σ : Tree A f) 
      → μ σ (λ p → η (Typ σ p) (Inh σ p)) ↦ σ
    {-# REWRITE μ-unit-r #-}

  η (● a₀ ▸ a₁) τ = cns τ (nil a₁)
  η (f ∣ σ ▸ τ) θ =
    let η-dec p = η (Typ σ p) (Inh σ p)
        lf-dec p = lf (Typ σ p) (Inh σ p)
    in nd f σ τ θ η-dec lf-dec

  μ = {!!}
  γ = {!!}
