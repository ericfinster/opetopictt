{-# OPTIONS --without-K --rewriting #-}

open import Base

module OpetopicType where

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
    ● : Frm A O 
    _∣_▸_ : {n : ℕ} (f : Frm A n)
      → (σ : Tree A f) (τ : Cell A f)
      → Frm A (S n)

  η : {A : Set} {n : ℕ} (f : Frm A n)
    → Cell A f → Tree A f

  η-pos : {A : Set} {n : ℕ}
    → (f : Frm A n) (α : Cell A f)
    → Pos (η f α)

  η-pos-elim : {A : Set} {n : ℕ}
    → (f : Frm A n) (α : Cell A f)
    → (X : (p : Pos (η f α)) → Set)
    → (η-pos* : X (η-pos f α))
    → (p : Pos (η f α)) → X p

  μ : {A : Set} {n : ℕ} {f : Frm A n}
    → (σ : Tree A f)
    → (δ : (p : Pos σ) → Tree A (Typ σ p))
    → Tree A f

  μ-pos : {A : Set} {n : ℕ}
    → {f : Frm A n} (σ : Tree A f)
    → (δ : (p : Pos σ) → Tree A (Typ σ p))
    → (p : Pos σ) (q : Pos (δ p))
    → Pos (μ σ δ)

  μ-pos-fst : {A : Set} {n : ℕ}
    → {f : Frm A n} (σ : Tree A f)
    → (δ : (p : Pos σ) → Tree A (Typ σ p))
    → Pos (μ σ δ) → Pos σ

  μ-pos-snd : {A : Set} {n : ℕ}
    → {f : Frm A n} (σ : Tree A f)
    → (δ : (p : Pos σ) → Tree A (Typ σ p))
    → (p : Pos (μ σ δ)) → Pos (δ (μ-pos-fst σ δ p))

  γ : {A : Set} {n : ℕ} {f : Frm A n}
    → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∣ σ ▸ τ))
    → (δ : (p : Pos σ) → Tree A (Typ σ p))
    → (ε : (p : Pos σ) → Tree A (Typ σ p ∣ δ p ▸ Inh σ p))
    → Tree A (f ∣ μ σ δ ▸ τ)

  γ-pos-inl : {A : Set} {n : ℕ} {f : Frm A n}
    → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∣ σ ▸ τ))
    → (ϕ : (p : Pos σ) → Tree A (Typ σ p))
    → (ψ : (p : Pos σ) → Tree A (Typ σ p ∣ ϕ p ▸ Inh σ p))
    → Pos ρ → Pos (γ σ τ ρ ϕ ψ)

  γ-pos-inr : {A : Set} {n : ℕ} {f : Frm A n}
    → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∣ σ ▸ τ))
    → (ϕ : (p : Pos σ) → Tree A (Typ σ p))
    → (ψ : (p : Pos σ) → Tree A (Typ σ p ∣ ϕ p ▸ Inh σ p))
    → (p : Pos σ) (q : Pos (ψ p))
    → Pos (γ σ τ ρ ϕ ψ)

  γ-pos-elim : {A : Set} {n : ℕ} {f : Frm A n}
    → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∣ σ ▸ τ))
    → (ϕ : (p : Pos σ) → Tree A (Typ σ p))
    → (ψ : (p : Pos σ) → Tree A (Typ σ p ∣ ϕ p ▸ Inh σ p))
    → (X : Pos (γ σ τ ρ ϕ ψ) → Set)
    → (inl* : (p : Pos ρ) → X (γ-pos-inl σ τ ρ ϕ ψ p))
    → (inr* : (p : Pos σ) (q : Pos (ψ p)) → X (γ-pos-inr σ τ ρ ϕ ψ p q))
    → (p : Pos (γ σ τ ρ ϕ ψ)) → X p

  data Tree A where
    ob : (α : Cell A ●) → Tree A ●
    lf : {n : ℕ} (f : Frm A n) (α : Cell A f)
      → Tree A (f ∣ η f α ▸ α)
    nd : {n : ℕ} (f : Frm A n) 
      → (σ : Tree A f) (τ : Cell A f)  (α : Cell A (f ∣ σ ▸ τ))
      → (δ : (p : Pos σ) → Tree A (Typ σ p))
      → (ε : (p : Pos σ) → Tree A (Typ σ p ∣ δ p ▸ Inh σ p))
      → Tree A (f ∣ μ σ δ ▸ τ)

  Pos (ob α) = ⊤
  Pos (lf f α) = ⊥
  Pos (nd f σ τ α δ ε) =
    ⊤ ⊔ Σ (Pos σ) (λ p → Pos (ε p))

  Typ (ob α) p = ●
  Typ (lf f α) ()
  Typ (nd f σ τ α δ ε) (inl unit) = f ∣ σ ▸ τ
  Typ (nd f σ τ α δ ε) (inr (p , q)) = Typ (ε p) q
  
  Inh (ob α) p = α
  Inh (lf f α) ()
  Inh (nd f σ τ α δ ε) (inl unit) = α
  Inh (nd f σ τ α δ ε) (inr (p , q)) = Inh (ε p) q

  postulate

    -- η-pos laws
    η-pos-typ : {A : Set} {n : ℕ}
      → (f : Frm A n) (α : Cell A f)
      → (p : Pos (η f α))
      → Typ (η f α) p ↦ f
    {-# REWRITE η-pos-typ #-}

    η-pos-inh : {A : Set} {n : ℕ}
      → (f : Frm A n) (α : Cell A f)
      → (p : Pos (η f α))
      → Inh (η f α) (η-pos f α) ↦ α
    {-# REWRITE η-pos-inh #-}

    η-pos-elim-β : {A : Set} {n : ℕ}
      → (f : Frm A n) (α : Cell A f)
      → (X : (p : Pos (η f α)) → Set)
      → (η-pos* : X (η-pos f α))
      → η-pos-elim f α X η-pos* (η-pos f α) ↦ η-pos*
    {-# REWRITE η-pos-elim-β #-}

    -- μ-pos laws
    μ-pos-typ : {A : Set} {n : ℕ} (f : Frm A n) (σ : Tree A f)
      → (δ : (p : Pos σ) → Tree A (Typ σ p))
      → (p : Pos (μ σ δ))
      → Typ (μ σ δ) p ↦ Typ (δ (μ-pos-fst σ δ p)) (μ-pos-snd σ δ p)
    {-# REWRITE μ-pos-typ #-}

    μ-pos-inh : {A : Set} {n : ℕ} (f : Frm A n) (σ : Tree A f)
      → (δ : (p : Pos σ) → Tree A (Typ σ p))
      → (p : Pos (μ σ δ))
      → Inh (μ σ δ) p ↦ Inh (δ (μ-pos-fst σ δ p)) (μ-pos-snd σ δ p)
    {-# REWRITE μ-pos-inh #-}
    
    μ-pos-fst-β : {A : Set} {n : ℕ} (f : Frm A n) (σ : Tree A f)
      → (δ : (p : Pos σ) → Tree A (Typ σ p))
      → (p : Pos σ) (q : Pos (δ p))
      → μ-pos-fst σ δ (μ-pos σ δ p q) ↦ p
    {-# REWRITE μ-pos-fst-β #-}

    μ-pos-snd-β : {A : Set} {n : ℕ} (f : Frm A n) (σ : Tree A f)
      → (δ : (p : Pos σ) → Tree A (Typ σ p))
      → (p : Pos σ) (q : Pos (δ p))
      → μ-pos-snd σ δ (μ-pos σ δ p q) ↦ q
    {-# REWRITE μ-pos-snd-β #-}

    μ-pos-η : {A : Set} {n : ℕ} (f : Frm A n) (σ : Tree A f)
      → (δ : (p : Pos σ) → Tree A (Typ σ p))
      → (p : Pos (μ σ δ))
      → μ-pos σ δ (μ-pos-fst σ δ p) (μ-pos-snd σ δ p) ↦ p
    {-# REWRITE μ-pos-η #-}

    -- μ laws
    μ-unit-r : {A : Set} {n : ℕ}
      → (f : Frm A n) (σ : Tree A f) 
      → μ σ (λ p → η (Typ σ p) (Inh σ p)) ↦ σ
    {-# REWRITE μ-unit-r #-}

    μ-unit-l : {A : Set} {n : ℕ}
      → (f : Frm A n) (α : Cell A f)
      → (δ : (p : Pos (η f α)) → Tree A (Typ (η f α) p))
      → μ (η f α) δ ↦ δ (η-pos f α)
    {-# REWRITE μ-unit-l #-}

    μ-assoc : {A : Set} {n : ℕ}
      → (f : Frm A n) (σ : Tree A f)
      → (δ : (p : Pos σ) → Tree A (Typ σ p))
      → (ε : (p : Pos (μ σ δ)) → Tree A (Typ (μ σ δ) p))
      → μ (μ σ δ) ε ↦ μ σ (λ p → μ (δ p) (λ q → ε (μ-pos σ δ p q)))
    {-# REWRITE μ-assoc #-}

    -- γ elim comp rules
    γ-pos-elim-inl-β : {A : Set} {n : ℕ} {f : Frm A n}
      → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∣ σ ▸ τ))
      → (ϕ : (p : Pos σ) → Tree A (Typ σ p))
      → (ψ : (p : Pos σ) → Tree A (Typ σ p ∣ ϕ p ▸ Inh σ p))
      → (X : Pos (γ σ τ ρ ϕ ψ) → Set)
      → (inl* : (p : Pos ρ) → X (γ-pos-inl σ τ ρ ϕ ψ p))
      → (inr* : (p : Pos σ) (q : Pos (ψ p)) → X (γ-pos-inr σ τ ρ ϕ ψ p q))
      → (p : Pos ρ)
      → γ-pos-elim σ τ ρ ϕ ψ X inl* inr* (γ-pos-inl σ τ ρ ϕ ψ p) ↦ inl* p
    {-# REWRITE γ-pos-elim-inl-β #-}

    γ-pos-elim-inr-β : {A : Set} {n : ℕ} {f : Frm A n}
      → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∣ σ ▸ τ))
      → (ϕ : (p : Pos σ) → Tree A (Typ σ p))
      → (ψ : (p : Pos σ) → Tree A (Typ σ p ∣ ϕ p ▸ Inh σ p))
      → (X : Pos (γ σ τ ρ ϕ ψ) → Set)
      → (inl* : (p : Pos ρ) → X (γ-pos-inl σ τ ρ ϕ ψ p))
      → (inr* : (p : Pos σ) (q : Pos (ψ p)) → X (γ-pos-inr σ τ ρ ϕ ψ p q))
      → (p : Pos σ) (q : Pos (ψ p))
      → γ-pos-elim σ τ ρ ϕ ψ X inl* inr* (γ-pos-inr σ τ ρ ϕ ψ p q) ↦ inr* p q
    {-# REWRITE γ-pos-elim-inr-β #-}

  η ● α = ob α
  η (f ∣ σ ▸ τ) α =
    let η-dec p = η (Typ σ p) (Inh σ p)
        lf-dec p = lf (Typ σ p) (Inh σ p)
    in nd f σ τ α η-dec lf-dec

  η-pos ● α = unit
  η-pos (f ∣ σ ▸ τ) α =
    inl unit

  η-pos-elim ● α X η-pos* unit = η-pos*
  η-pos-elim (f ∣ σ ▸ τ) α X η-pos* (inl unit) = η-pos*
  
  μ (ob α) κ = κ unit
  μ (lf f α) κ = lf f α
  μ (nd f σ τ α δ ε) κ =
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μ (ε p) (κ↑ p) 
    in γ σ τ w δ ψ

  μ-pos (ob α) κ unit q = q
  μ-pos (lf f α) κ p q = p
  μ-pos (nd f σ τ α δ ε) κ (inl unit) r = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μ (ε p) (κ↑ p) 
    in γ-pos-inl σ τ w δ ψ r
  μ-pos (nd f σ τ α δ ε) κ (inr (p , q)) r = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μ (ε p) (κ↑ p) 
    in γ-pos-inr σ τ w δ ψ p (μ-pos (ε p) (κ↑ p) q r)

  μ-pos-fst (ob α) κ p = unit
  μ-pos-fst (lf f α) κ p = p
  μ-pos-fst (nd f σ τ α δ ε) κ p = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μ (ε p) (κ↑ p)
        inl* p = inl unit
        inr* p q = inr (p , μ-pos-fst (ε p) (κ↑ p) q)
    in γ-pos-elim σ τ w δ ψ _ inl* inr* p

  μ-pos-snd (ob α) κ p = p
  μ-pos-snd (lf f α) κ ()
  μ-pos-snd (nd f σ τ α δ ε) κ p = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μ (ε p) (κ↑ p)
        inl* p = p
        inr* p q = μ-pos-snd (ε p) (κ↑ p) q
        X p = Pos (κ (μ-pos-fst (nd f σ τ α δ ε) κ p))
    in γ-pos-elim σ τ w δ ψ X inl* inr* p

  γ .(η f τ) .τ (lf f τ) ϕ ψ = ψ (η-pos f τ)
  γ .(μ σ δ) .τ (nd f σ τ α δ ε) ϕ ψ = 
    let ϕ↑ p q = ϕ (μ-pos σ δ p q)
        ψ↑ p q = ψ (μ-pos σ δ p q)
        δ↑ p = μ (δ p) (ϕ↑ p)
        ε↑ p = γ (δ p) (Inh σ p) (ε p) (ϕ↑ p) (ψ↑ p)
    in nd f σ τ α δ↑ ε↑

  γ-pos-inl .(η f τ) .τ (lf f τ) ϕ ψ ()
  γ-pos-inl .(μ σ δ) .τ (nd f σ τ α δ ε) ϕ ψ (inl unit) = inl unit
  γ-pos-inl .(μ σ δ) .τ (nd f σ τ α δ ε) ϕ ψ (inr (p , q)) = 
    let ϕ↑ p q = ϕ (μ-pos σ δ p q)
        ψ↑ p q = ψ (μ-pos σ δ p q)
        δ↑ p = μ (δ p) (ϕ↑ p)
        ε↑ p = γ (δ p) (Inh σ p) (ε p) (ϕ↑ p) (ψ↑ p)
    in inr (p , γ-pos-inl (δ p) (Inh σ p) (ε p) (ϕ↑ p) (ψ↑ p) q)

  γ-pos-inr .(η f τ) .τ (lf f τ) ϕ ψ p q =
    η-pos-elim f τ (λ p → Pos (ψ p) → Pos (ψ (η-pos f τ))) (λ p → p) p q
  γ-pos-inr  .(μ σ δ) .τ (nd f σ τ α δ ε) ϕ ψ p q = 
    let ϕ↑ p q = ϕ (μ-pos σ δ p q)
        ψ↑ p q = ψ (μ-pos σ δ p q)
        δ↑ p = μ (δ p) (ϕ↑ p)
        ε↑ p = γ (δ p) (Inh σ p) (ε p) (ϕ↑ p) (ψ↑ p)
        p₀ = μ-pos-fst σ δ p
        p₁ = μ-pos-snd σ δ p
    in inr (p₀ , (γ-pos-inr (δ p₀) (Inh σ p₀) (ε p₀) (ϕ↑ p₀) (ψ↑ p₀) p₁ q))

  γ-pos-elim .(η f τ) .τ (lf f τ) ϕ ψ X inl* inr* p = inr* (η-pos f τ) p
  γ-pos-elim .(μ σ δ) .τ (nd f σ τ α δ ε) ϕ ψ X inl* inr* (inl unit) = inl* (inl unit)
  γ-pos-elim .(μ σ δ) .τ (nd f σ τ α δ ε) ϕ ψ X inl* inr* (inr (p , q)) = 
    let ϕ↑ p q = ϕ (μ-pos σ δ p q)
        ψ↑ p q = ψ (μ-pos σ δ p q)
        δ↑ p = μ (δ p) (ϕ↑ p)
        ε↑ p = γ (δ p) (Inh σ p) (ε p) (ϕ↑ p) (ψ↑ p)
    in γ-pos-elim (δ p) (Inh σ p) (ε p) (ϕ↑ p) (ψ↑ p)
                  (λ q → X (inr (p , q))) (λ q → inl* (inr (p , q)))
                  (λ p₀ q₀ → inr* (μ-pos σ δ p p₀) q₀) q
