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
    ●_▸_ : (a₀ : A) → (a₁ : A) → Frm A O 
    _∣_▸_ : {n : ℕ} (f : Frm A n)
      → (σ : Tree A f) (τ : Cell A f)
      → Frm A (S n)

  η : {A : Set} {n : ℕ} (f : Frm A n)
    → Cell A f → Tree A f

  η-pos : {A : Set} {n : ℕ}
    → (f : Frm A n) (τ : Cell A f)
    → Pos (η f τ)

  η-pos-elim : {A : Set} {n : ℕ}
    → (f : Frm A n) (τ : Cell A f)
    → (X : (p : Pos (η f τ)) → Set)
    → (η-pos* : X (η-pos f τ))
    → (p : Pos (η f τ)) → X p

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

  α : {A : Set} {a₀ a₁ a₂ : A}
    → Tree A (● a₀ ▸ a₁)
    → Tree A (● a₁ ▸ a₂)
    → Tree A (● a₀ ▸ a₂)

  α-pos-inl : {A : Set} {a₀ a₁ a₂ : A}
    → {σ₀ : Tree A (● a₀ ▸ a₁)}
    → {σ₁ : Tree A (● a₁ ▸ a₂)}
    → Pos σ₀ → Pos (α σ₀ σ₁)

  α-pos-inr : {A : Set} {a₀ a₁ a₂ : A}
    → {σ₀ : Tree A (● a₀ ▸ a₁)}
    → {σ₁ : Tree A (● a₁ ▸ a₂)}
    → Pos σ₁ → Pos (α σ₀ σ₁)

  α-pos-elim : {A : Set} {a₀ a₁ a₂ : A}
    → (σ₀ : Tree A (● a₀ ▸ a₁))
    → (σ₁ : Tree A (● a₁ ▸ a₂))
    → (X : Pos (α σ₀ σ₁) → Set)
    → (inl* : (p : Pos σ₀) → X (α-pos-inl p))
    → (inr* : (p : Pos σ₁) → X (α-pos-inr p))
    → (p : Pos (α σ₀ σ₁)) → X p

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

    -- η-pos laws
    η-pos-typ : {A : Set} {n : ℕ}
      → (f : Frm A n) (τ : Cell A f)
      → (p : Pos (η f τ))
      → Typ (η f τ) p ↦ f
    {-# REWRITE η-pos-typ #-}

    η-pos-inh : {A : Set} {n : ℕ}
      → (f : Frm A n) (τ : Cell A f)
      → (p : Pos (η f τ))
      → Inh (η f τ) p ↦ τ
    {-# REWRITE η-pos-inh #-}

    η-pos-elim-β : {A : Set} {n : ℕ}
      → (f : Frm A n) (τ : Cell A f)
      → (X : (p : Pos (η f τ)) → Set)
      → (η-pos* : X (η-pos f τ))
      → η-pos-elim f τ X η-pos* (η-pos f τ) ↦ η-pos*
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
      → (f : Frm A n) (τ : Cell A f)
      → (δ : (p : Pos (η f τ)) → Tree A (Typ (η f τ) p))
      → μ (η f τ) δ ↦ δ (η-pos f τ)
    {-# REWRITE μ-unit-l #-}

    μ-assoc : {A : Set} {n : ℕ}
      → (f : Frm A n) (σ : Tree A f)
      → (δ : (p : Pos σ) → Tree A (Typ σ p))
      → (ε : (p : Pos (μ σ δ)) → Tree A (Typ (μ σ δ) p))
      → μ (μ σ δ) ε ↦ μ σ (λ p → μ (δ p) (λ q → ε (μ-pos σ δ p q)))
    {-# REWRITE μ-assoc #-}

    -- α elim comp rules
    α-pos-elim-inl-β : {A : Set} {a₀ a₁ a₂ : A}
      → (σ₀ : Tree A (● a₀ ▸ a₁))
      → (σ₁ : Tree A (● a₁ ▸ a₂))
      → (X : Pos (α σ₀ σ₁) → Set)
      → (inl* : (p : Pos σ₀) → X (α-pos-inl p))
      → (inr* : (p : Pos σ₁) → X (α-pos-inr p))
      → (p : Pos σ₀)
      → α-pos-elim σ₀ σ₁ X inl* inr* (α-pos-inl p) ↦ inl* p
    {-# REWRITE α-pos-elim-inl-β #-}
    
    α-pos-elim-inr-β : {A : Set} {a₀ a₁ a₂ : A}
      → (σ₀ : Tree A (● a₀ ▸ a₁))
      → (σ₁ : Tree A (● a₁ ▸ a₂))
      → (X : Pos (α σ₀ σ₁) → Set)
      → (inl* : (p : Pos σ₀) → X (α-pos-inl p))
      → (inr* : (p : Pos σ₁) → X (α-pos-inr p))
      → (p : Pos σ₁)
      → α-pos-elim σ₀ σ₁ X inl* inr* (α-pos-inr p) ↦ inr* p
    {-# REWRITE α-pos-elim-inr-β #-}
      
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

  η (● a₀ ▸ a₁) τ = cns τ (nil a₁)
  η (f ∣ σ ▸ τ) θ =
    let η-dec p = η (Typ σ p) (Inh σ p)
        lf-dec p = lf (Typ σ p) (Inh σ p)
    in nd f σ τ θ η-dec lf-dec

  η-pos (● a₀ ▸ a₁) τ = inl unit
  η-pos (f ∣ σ ▸ τ) θ = inl unit
  
  η-pos-elim (● a₀ ▸ a₁) τ X η-pos* (inl unit) = η-pos*
  η-pos-elim (f ∣ σ ▸ τ) θ X η-pos* (inl unit) = η-pos*

  α (nil _) y = y
  α (cns ρ x) y = cns ρ (α x y)

  α-pos-inl {σ₀ = cns ρ σ₀} (inl unit) = inl unit
  α-pos-inl {σ₀ = cns ρ σ₀} (inr p) = inr (α-pos-inl p)

  α-pos-inr {σ₀ = nil _} p = p
  α-pos-inr {σ₀ = cns ρ σ₀} p =
    inr (α-pos-inr p)

  α-pos-elim (nil _) σ₁ X inl* inr* = inr*
  α-pos-elim (cns ρ σ₀) σ₁ X inl* inr* (inl unit) = inl* (inl unit)
  α-pos-elim (cns ρ σ₀) σ₁ X inl* inr* (inr p) =
    α-pos-elim σ₀ σ₁ (λ p → X (inr p)) (λ p → inl* (inr p)) inr* p

  μ (nil a) κ = nil a
  μ (cns ρ σ) κ =
    let w = κ (inl unit)
        κ↑ p = κ (inr p)
    in α w (μ σ κ↑)
  μ (lf f τ) κ = lf f τ
  μ (nd f σ τ θ δ ε) κ =
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μ (ε p) (κ↑ p) 
    in γ σ τ w δ ψ

  μ-pos (cns ρ σ) κ (inl unit) q = α-pos-inl q
  μ-pos (cns ρ σ) κ (inr p) q =
    let w = κ (inl unit)
        κ↑ p = κ (inr p)
    in α-pos-inr (μ-pos σ κ↑ p q)
  μ-pos (nd f σ τ θ δ ε) κ (inl unit) r = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μ (ε p) (κ↑ p) 
    in γ-pos-inl σ τ w δ ψ r
  μ-pos (nd f σ τ θ δ ε) κ (inr (p , q)) r = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μ (ε p) (κ↑ p) 
    in γ-pos-inr σ τ w δ ψ p (μ-pos (ε p) (κ↑ p) q r)

  μ-pos-fst (cns ρ σ) κ p =
    let w = κ (inl unit)
        κ↑ p = κ (inr p)
        X p = ⊤ ⊔ Pos σ
        inl* p = inl unit
        inr* p = inr (μ-pos-fst σ κ↑ p)
    in α-pos-elim w (μ σ κ↑) X inl* inr* p
  μ-pos-fst (nd f σ τ θ δ ε) κ p = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μ (ε p) (κ↑ p)
        inl* p = inl unit
        inr* p q = inr (p , μ-pos-fst (ε p) (κ↑ p) q)
    in γ-pos-elim σ τ w δ ψ _ inl* inr* p

  μ-pos-snd (cns ρ σ) κ p = 
    let w = κ (inl unit)
        κ↑ p = κ (inr p)
        X p = Pos (κ (μ-pos-fst (cns ρ σ) κ p))
        inl* p = p
        inr* p = μ-pos-snd σ κ↑ p
    in α-pos-elim w (μ σ κ↑) X inl* inr* p
  μ-pos-snd (nd f σ τ θ δ ε) κ p = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μ (ε p) (κ↑ p)
        X p = Pos (κ (μ-pos-fst (nd f σ τ θ δ ε) κ p))
        inl* p = p
        inr* p q = μ-pos-snd (ε p) (κ↑ p) q
    in γ-pos-elim σ τ w δ ψ X inl* inr* p

  γ .(η f τ) .τ (lf f τ) ϕ ψ = ψ (η-pos f τ)
  γ .(μ σ δ) .τ (nd f σ τ θ δ ε) ϕ ψ = 
    let ϕ↑ p q = ϕ (μ-pos σ δ p q)
        ψ↑ p q = ψ (μ-pos σ δ p q)
        δ↑ p = μ (δ p) (ϕ↑ p)
        ε↑ p = γ (δ p) (Inh σ p) (ε p) (ϕ↑ p) (ψ↑ p)
    in nd f σ τ θ δ↑ ε↑

  γ-pos-inl .(η f τ) .τ (lf f τ) ϕ ψ ()
  γ-pos-inl .(μ σ δ) .τ (nd f σ τ θ δ ε) ϕ ψ (inl unit) = inl unit
  γ-pos-inl .(μ σ δ) .τ (nd f σ τ θ δ ε) ϕ ψ (inr (p , q)) = 
    let ϕ↑ p q = ϕ (μ-pos σ δ p q)
        ψ↑ p q = ψ (μ-pos σ δ p q)
        δ↑ p = μ (δ p) (ϕ↑ p)
        ε↑ p = γ (δ p) (Inh σ p) (ε p) (ϕ↑ p) (ψ↑ p)
    in inr (p , γ-pos-inl (δ p) (Inh σ p) (ε p) (ϕ↑ p) (ψ↑ p) q)

  γ-pos-inr .(η f τ) .τ (lf f τ) ϕ ψ p q =
    η-pos-elim f τ (λ p → Pos (ψ p) → Pos (ψ (η-pos f τ))) (λ p → p) p q
  γ-pos-inr  .(μ σ δ) .τ (nd f σ τ θ δ ε) ϕ ψ p q = 
    let ϕ↑ p q = ϕ (μ-pos σ δ p q)
        ψ↑ p q = ψ (μ-pos σ δ p q)
        δ↑ p = μ (δ p) (ϕ↑ p)
        ε↑ p = γ (δ p) (Inh σ p) (ε p) (ϕ↑ p) (ψ↑ p)
        p₀ = μ-pos-fst σ δ p
        p₁ = μ-pos-snd σ δ p
    in inr (p₀ , (γ-pos-inr (δ p₀) (Inh σ p₀) (ε p₀) (ϕ↑ p₀) (ψ↑ p₀) p₁ q))

  γ-pos-elim .(η f τ) .τ (lf f τ) ϕ ψ X inl* inr* p = inr* (η-pos f τ) p
  γ-pos-elim .(μ σ δ) .τ (nd f σ τ θ δ ε) ϕ ψ X inl* inr* (inl unit) = inl* (inl unit)
  γ-pos-elim .(μ σ δ) .τ (nd f σ τ θ δ ε) ϕ ψ X inl* inr* (inr (p , q)) = 
    let ϕ↑ p q = ϕ (μ-pos σ δ p q)
        ψ↑ p q = ψ (μ-pos σ δ p q)
        δ↑ p = μ (δ p) (ϕ↑ p)
        ε↑ p = γ (δ p) (Inh σ p) (ε p) (ϕ↑ p) (ψ↑ p)
    in γ-pos-elim (δ p) (Inh σ p) (ε p) (ϕ↑ p) (ψ↑ p)
                  (λ q → X (inr (p , q))) (λ q → inl* (inr (p , q)))
                  (λ p₀ q₀ → inr* (μ-pos σ δ p p₀) q₀) q

