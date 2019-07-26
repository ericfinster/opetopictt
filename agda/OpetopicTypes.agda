{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module OpetopicTypes where

  postulate

    𝕆 : Type₀

  data Frm (A : 𝕆) : ℕ → Type₀
  data Tree (A : 𝕆) : {n : ℕ} (f : Frm A n) → Type₀

  postulate
  
    Cell : (A : 𝕆) {n : ℕ} (f : Frm A n) → Type₀
    Pos : {A : 𝕆} {n : ℕ} {f : Frm A n} → Tree A f → Type₀

  Typ : {A : 𝕆} {n : ℕ} {f : Frm A n}
    → (σ : Tree A f) (p : Pos σ) → Frm A n
    
  Inh : {A : 𝕆} {n : ℕ} {f : Frm A n}
    → (σ : Tree A f) (p : Pos σ) → Cell A (Typ σ p)

  data Frm (A : 𝕆) where
    ● : Frm A O
    _∥_▸_ : {n : ℕ} (f : Frm A n) (σ : Tree A f) (τ : Cell A f) → Frm A (S n)

  η : {A : 𝕆} {n : ℕ} {f : Frm A n} → Cell A f → Tree A f

  μ : {A : 𝕆} {n : ℕ} {f : Frm A n} (σ : Tree A f)
    → (κ : (p : Pos σ) → Tree A (Typ σ p))
    → Tree A f

  γ : {A : 𝕆} {n : ℕ} {f : Frm A n}
    → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
    → (ϕ : (p : Pos σ) → Tree A (Typ σ p))
    → (ψ : (p : Pos σ) → Tree A (Typ σ p ∥ ϕ p ▸ Inh σ p))
    → Tree A (f ∥ μ σ ϕ ▸ τ)

  η-pos : {A : 𝕆} {n : ℕ} {f : Frm A n}
    → (α : Cell A f) → Pos (η α)

  η-pos-elim : {A : 𝕆} {n : ℕ} {f : Frm A n} (α : Cell A f)
    → (X : (p : Pos (η α)) → Type₀)
    → (η-pos* : X (η-pos α))
    → (p : Pos (η α)) → X p

  μ-pos : {A : 𝕆} {n : ℕ} {f : Frm A n} (σ : Tree A f)
    → (κ : (p : Pos σ) → Tree A (Typ σ p))
    → (p : Pos σ) (q : Pos (κ p))
    → Pos (μ σ κ)

  μ-pos-fst : {A : 𝕆} {n : ℕ} {f : Frm A n} (σ : Tree A f)
    → (κ : (p : Pos σ) → Tree A (Typ σ p))
    → Pos (μ σ κ) → Pos σ

  μ-pos-snd : {A : 𝕆} {n : ℕ} {f : Frm A n} (σ : Tree A f)
    → (κ : (p : Pos σ) → Tree A (Typ σ p))
    → (p : Pos (μ σ κ)) → Pos (κ (μ-pos-fst σ κ p))

  γ-pos-inl : {A : 𝕆} {n : ℕ} {f : Frm A n}
    → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
    → (ϕ : (p : Pos σ) → Tree A (Typ σ p))
    → (ψ : (p : Pos σ) → Tree A (Typ σ p ∥ ϕ p ▸ Inh σ p))
    → Pos ρ → Pos (γ σ τ ρ ϕ ψ)

  γ-pos-inr : {A : 𝕆} {n : ℕ} {f : Frm A n}
    → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
    → (ϕ : (p : Pos σ) → Tree A (Typ σ p))
    → (ψ : (p : Pos σ) → Tree A (Typ σ p ∥ ϕ p ▸ Inh σ p))
    → (p : Pos σ) (q : Pos (ψ p))
    → Pos (γ σ τ ρ ϕ ψ)

  γ-pos-elim : {A : 𝕆} {n : ℕ} {f : Frm A n}
    → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
    → (ϕ : (p : Pos σ) → Tree A (Typ σ p))
    → (ψ : (p : Pos σ) → Tree A (Typ σ p ∥ ϕ p ▸ Inh σ p))
    → (X : Pos (γ σ τ ρ ϕ ψ) → Type₀)
    → (inl* : (p : Pos ρ) → X (γ-pos-inl σ τ ρ ϕ ψ p))
    → (inr* : (p : Pos σ) (q : Pos (ψ p)) → X (γ-pos-inr σ τ ρ ϕ ψ p q))
    → (p : Pos (γ σ τ ρ ϕ ψ)) → X p

  data Tree (A : 𝕆) where
    ob : (α : Cell A ●) → Tree A ●
    lf : {n : ℕ} (f : Frm A n) (α : Cell A f)
      → Tree A (f ∥ η α ▸ α)
    nd : {n : ℕ} {f : Frm A n} 
      → (σ : Tree A f) (τ : Cell A f)  (α : Cell A (f ∥ σ ▸ τ))
      → (δ : (p : Pos σ) → Tree A (Typ σ p))
      → (ε : (p : Pos σ) → Tree A (Typ σ p ∥ δ p ▸ Inh σ p))
      → Tree A (f ∥ μ σ δ ▸ τ)

  postulate

    ob-pos : {A : 𝕆} (α : Cell A ●)
      → Pos (ob α)

    ob-pos-elim : {A : 𝕆} (α : Cell A ●)
      → (X : Pos (ob α) → Type₀)
      → (x : X (ob-pos α))
      → (p : Pos (ob α)) → X p

    ob-pos-elim-β : {A : 𝕆} (α : Cell A ●)
      → (X : Pos (ob α) → Type₀)
      → (x : X (ob-pos α))
      → ob-pos-elim α X x (ob-pos α) ↦ x
    {-# REWRITE ob-pos-elim-β #-}

    lf-pos-elim : {A : 𝕆} {n : ℕ} (f : Frm A n) (α : Cell A f)
      → (X : Pos (lf f α) → Type₀)
      → (p : Pos (lf f α)) → X p

    nd-pos-here : {A : 𝕆} {n : ℕ} {f : Frm A n} 
      → (σ : Tree A f) (τ : Cell A f)  (α : Cell A (f ∥ σ ▸ τ))
      → (δ : (p : Pos σ) → Tree A (Typ σ p))
      → (ε : (p : Pos σ) → Tree A (Typ σ p ∥ δ p ▸ Inh σ p))
      → Pos (nd σ τ α δ ε)

    nd-pos-there : {A : 𝕆} {n : ℕ} {f : Frm A n} 
      → (σ : Tree A f) (τ : Cell A f)  (α : Cell A (f ∥ σ ▸ τ))
      → (δ : (p : Pos σ) → Tree A (Typ σ p))
      → (ε : (p : Pos σ) → Tree A (Typ σ p ∥ δ p ▸ Inh σ p))
      → (p : Pos σ) (q : Pos (ε p))
      → Pos (nd σ τ α δ ε)
      
    nd-pos-elim : {A : 𝕆} {n : ℕ} {f : Frm A n} 
      → (σ : Tree A f) (τ : Cell A f)  (α : Cell A (f ∥ σ ▸ τ))
      → (δ : (p : Pos σ) → Tree A (Typ σ p))
      → (ε : (p : Pos σ) → Tree A (Typ σ p ∥ δ p ▸ Inh σ p))
      → (X : Pos (nd σ τ α δ ε) → Type₀)
      → (here* : X (nd-pos-here σ τ α δ ε))
      → (there* : (p : Pos σ) (q : Pos (ε p))
           → X (nd-pos-there σ τ α δ ε p q))
      → (p : Pos (nd σ τ α δ ε)) → X p

    nd-pos-elim-here-β : {A : 𝕆} {n : ℕ} {f : Frm A n} 
      → (σ : Tree A f) (τ : Cell A f)  (α : Cell A (f ∥ σ ▸ τ))
      → (δ : (p : Pos σ) → Tree A (Typ σ p))
      → (ε : (p : Pos σ) → Tree A (Typ σ p ∥ δ p ▸ Inh σ p))
      → (X : Pos (nd σ τ α δ ε) → Type₀)
      → (here* : X (nd-pos-here σ τ α δ ε))
      → (there* : (p : Pos σ) (q : Pos (ε p))
           → X (nd-pos-there σ τ α δ ε p q))
      → nd-pos-elim σ τ α δ ε X here* there* (nd-pos-here σ τ α δ ε) ↦ here*
    {-# REWRITE nd-pos-elim-here-β #-}

    nd-pos-elim-there-β : {A : 𝕆} {n : ℕ} {f : Frm A n} 
      → (σ : Tree A f) (τ : Cell A f)  (α : Cell A (f ∥ σ ▸ τ))
      → (δ : (p : Pos σ) → Tree A (Typ σ p))
      → (ε : (p : Pos σ) → Tree A (Typ σ p ∥ δ p ▸ Inh σ p))
      → (X : Pos (nd σ τ α δ ε) → Type₀)
      → (here* : X (nd-pos-here σ τ α δ ε))
      → (there* : (p : Pos σ) (q : Pos (ε p))
           → X (nd-pos-there σ τ α δ ε p q))
      → (p : Pos σ) (q : Pos (ε p))
      → nd-pos-elim σ τ α δ ε X here* there* (nd-pos-there σ τ α δ ε p q) ↦ there* p q
    {-# REWRITE nd-pos-elim-there-β #-}

  --
  --  Definining position types and inhabitants
  --

  -- Typ : {A : 𝕆} {n : ℕ} {f : Frm A n}
  --   → (σ : Tree A f) (p : Pos σ) → Frm A n
  Typ (ob α) p = ●
  Typ (lf f α) = lf-pos-elim f α (λ _ → Frm _ _)
  Typ (nd {f = f} σ τ α δ ε) =
    let X p = Frm _ _
        th p q = Typ {f = Typ σ p ∥ δ p ▸ Inh σ p} (ε p) q
    in nd-pos-elim σ τ α δ ε X (f ∥ σ ▸ τ) th

  -- Inh : {A : 𝕆} {n : ℕ} {f : Frm A n}
  --   → (σ : Tree A f) (p : Pos σ) → Cell A (Typ σ p)
  Inh (ob α) p = α
  Inh (lf f α) =
    let X p = Cell _ (Typ {f = f ∥ η α ▸ α} (lf f α) p)
    in lf-pos-elim f α X
  Inh (nd {f = f} σ τ α δ ε) =
    let X p = Cell _ (Typ {f = f ∥ μ σ δ ▸ τ} (nd σ τ α δ ε) p)
        th p q = Inh {f = Typ σ p ∥ δ p ▸ Inh σ p} (ε p) q
    in nd-pos-elim σ τ α δ ε X α th

  postulate

    -- η-pos laws
    η-pos-typ : {A : 𝕆} {n : ℕ} {f : Frm A n}
      → (α : Cell A f) (p : Pos (η α))
      → Typ (η α) p ↦ f
    {-# REWRITE η-pos-typ #-}

    η-pos-inh : {A : 𝕆} {n : ℕ} {f : Frm A n}
      → (α : Cell A f) (p : Pos (η α))
      → Inh (η α) (η-pos α) ↦ α
    {-# REWRITE η-pos-inh #-}

    η-pos-elim-β : {A : 𝕆} {n : ℕ} {f : Frm A n} (α : Cell A f)
      → (X : (p : Pos (η α)) → Type₀)
      → (η-pos* : X (η-pos α))
      → η-pos-elim α X η-pos* (η-pos α) ↦ η-pos*
    {-# REWRITE η-pos-elim-β #-}
    
    -- μ-pos laws
    μ-pos-typ : {A : 𝕆} {n : ℕ} {f : Frm A n} (σ : Tree A f)
      → (κ : (p : Pos σ) → Tree A (Typ σ p))
      → (p : Pos (μ σ κ))
      → Typ (μ σ κ) p ↦ Typ {f = Typ {f = f} σ (μ-pos-fst σ κ p)} (κ (μ-pos-fst σ κ p)) (μ-pos-snd σ κ p)
    {-# REWRITE μ-pos-typ #-}

    μ-pos-inh : {A : 𝕆} {n : ℕ} {f : Frm A n} (σ : Tree A f)
      → (κ : (p : Pos σ) → Tree A (Typ σ p))
      → (p : Pos (μ σ κ))
      → Inh (μ σ κ) p ↦ Inh (κ (μ-pos-fst σ κ p)) (μ-pos-snd σ κ p)
    {-# REWRITE μ-pos-inh #-}
    
    μ-pos-fst-β : {A : 𝕆} {n : ℕ} {f : Frm A n} (σ : Tree A f)
      → (κ : (p : Pos σ) → Tree A (Typ σ p))
      → (p : Pos σ) (q : Pos (κ p))
      → μ-pos-fst σ κ (μ-pos σ κ p q) ↦ p
    {-# REWRITE μ-pos-fst-β #-}

    μ-pos-snd-β : {A : 𝕆} {n : ℕ} {f : Frm A n} (σ : Tree A f)
      → (κ : (p : Pos σ) → Tree A (Typ σ p))
      → (p : Pos σ) (q : Pos (κ p))
      → μ-pos-snd σ κ (μ-pos σ κ p q) ↦ q
    {-# REWRITE μ-pos-snd-β #-}

    μ-pos-η : {A : 𝕆} {n : ℕ} {f : Frm A n} (σ : Tree A f)
      → (κ : (p : Pos σ) → Tree A (Typ σ p))
      → (p : Pos (μ σ κ))
      → μ-pos σ κ (μ-pos-fst σ κ p) (μ-pos-snd σ κ p) ↦ p
    {-# REWRITE μ-pos-η #-}

    -- μ laws
    μ-unit-r : {A : 𝕆} {n : ℕ} {f : Frm A n} (σ : Tree A f) 
      → μ σ (λ p → η (Inh σ p)) ↦ σ
    {-# REWRITE μ-unit-r #-}

    μ-unit-l : {A : 𝕆} {n : ℕ} {f : Frm A n}
      → (α : Cell A f) (κ : (p : Pos (η α)) → Tree A (Typ (η α) p))
      → μ (η α) κ ↦ κ (η-pos α)
    {-# REWRITE μ-unit-l #-}

    μ-assoc : {A : 𝕆} {n : ℕ} {f : Frm A n} (σ : Tree A f)
      → (κ : (p : Pos σ) → Tree A (Typ σ p))
      → (θ : (p : Pos (μ σ κ)) → Tree A (Typ (μ σ κ) p))
      → μ (μ σ κ) θ ↦ μ σ (λ p → μ (κ p) (λ q → θ (μ-pos σ κ p q)))
    {-# REWRITE μ-assoc #-}
    
    -- γ elim comp rules
    γ-pos-elim-inl-β : {A : 𝕆} {n : ℕ} {f : Frm A n}
      → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
      → (ϕ : (p : Pos σ) → Tree A (Typ σ p))
      → (ψ : (p : Pos σ) → Tree A (Typ σ p ∥ ϕ p ▸ Inh σ p))
      → (X : Pos (γ σ τ ρ ϕ ψ) → Type₀)
      → (inl* : (p : Pos ρ) → X (γ-pos-inl σ τ ρ ϕ ψ p))
      → (inr* : (p : Pos σ) (q : Pos (ψ p)) → X (γ-pos-inr σ τ ρ ϕ ψ p q))
      → (p : Pos ρ)
      → γ-pos-elim σ τ ρ ϕ ψ X inl* inr* (γ-pos-inl σ τ ρ ϕ ψ p) ↦ inl* p
    {-# REWRITE γ-pos-elim-inl-β #-}

    γ-pos-elim-inr-β : {A : 𝕆} {n : ℕ} {f : Frm A n}
      → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
      → (ϕ : (p : Pos σ) → Tree A (Typ σ p))
      → (ψ : (p : Pos σ) → Tree A (Typ σ p ∥ ϕ p ▸ Inh σ p))
      → (X : Pos (γ σ τ ρ ϕ ψ) → Type₀)
      → (inl* : (p : Pos ρ) → X (γ-pos-inl σ τ ρ ϕ ψ p))
      → (inr* : (p : Pos σ) (q : Pos (ψ p)) → X (γ-pos-inr σ τ ρ ϕ ψ p q))
      → (p : Pos σ) (q : Pos (ψ p))
      → γ-pos-elim σ τ ρ ϕ ψ X inl* inr* (γ-pos-inr σ τ ρ ϕ ψ p q) ↦ inr* p q
    {-# REWRITE γ-pos-elim-inr-β #-}
    
    -- γ pos laws
    γ-pos-typ : {A : 𝕆} {n : ℕ} {f : Frm A n}
      → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
      → (ϕ : (p : Pos σ) → Tree A (Typ σ p))
      → (ψ : (p : Pos σ) → Tree A (Typ σ p ∥ ϕ p ▸ Inh σ p))
      → (p : Pos (γ σ τ ρ ϕ ψ))
      → Typ (γ σ τ ρ ϕ ψ) p ↦
          γ-pos-elim σ τ ρ ϕ ψ (λ _ → Frm A (S n))
                     (λ p → Typ {f = f ∥ σ ▸ τ} ρ p)
                     (λ p q → Typ {f = Typ σ p ∥ ϕ p ▸ Inh σ p} (ψ p) q) p
    {-# REWRITE γ-pos-typ #-}

    -- γ laws
    γ-unit-r : {A : 𝕆} {n : ℕ} {f : Frm A n}
      → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
      → γ σ τ ρ (λ p → η (Inh σ p)) (λ p → lf (Typ σ p) (Inh σ p)) ↦ ρ
    {-# REWRITE γ-unit-r #-}

    -- Doesn't seem to be necessary for typechecking below, but ...
    γ-assoc : {A : 𝕆} {n : ℕ} {f : Frm A n}
      → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
      → (ϕ₀ : (p : Pos σ) → Tree A (Typ σ p))
      → (ψ₀ : (p : Pos σ) → Tree A (Typ σ p ∥ ϕ₀ p ▸ Inh σ p))
      → (ϕ₁ : (p : Pos (μ σ ϕ₀)) → Tree A (Typ (μ σ ϕ₀) p))
      → (ψ₁ : (p : Pos (μ σ ϕ₀)) → Tree A (Typ (μ σ ϕ₀) p ∥ ϕ₁ p ▸ Inh (μ σ ϕ₀) p))
      → γ (μ σ ϕ₀) τ (γ σ τ ρ ϕ₀ ψ₀) ϕ₁ ψ₁ ↦
        γ σ τ ρ (λ p → μ (ϕ₀ p) (λ q → ϕ₁ (μ-pos σ ϕ₀ p q)))
                (λ p → γ (ϕ₀ p) (Inh σ p) (ψ₀ p)
                         (λ q → ϕ₁ (μ-pos σ ϕ₀ p q))
                         (λ q → ψ₁ (μ-pos σ ϕ₀ p q)))

    -- Finally, it seems there should be the interchange law
    -- Is this sufficient?
    γμ-ichg : {A : 𝕆} {n : ℕ} {f : Frm A n}
      → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
      → (ϕ : (p : Pos σ) → Tree A (Typ σ p))
      → (ψ : (p : Pos σ) → Tree A (Typ σ p ∥ ϕ p ▸ Inh σ p))
      → (κ : (p : Pos ρ) → Tree A (Typ ρ p))
      → γ σ τ (μ ρ κ) ϕ ψ ↦
        μ (γ σ τ ρ ϕ ψ)
          (γ-pos-elim σ τ ρ ϕ ψ
            (λ p → Tree A (Typ (γ σ τ ρ ϕ ψ) p)) κ
            (λ p q → η (Inh (ψ p) q)))

  -- η : {A : 𝕆} {n : ℕ} {f : Frm A n} → Cell A f → Tree A f
  η {f = ●} α = ob α
  η {f = f ∥ σ ▸ τ} α =  
    let η-dec p = η (Inh σ p)
        lf-dec p = lf (Typ σ p) (Inh σ p)
    in nd σ τ α η-dec lf-dec

  -- η-pos : {A : 𝕆} {n : ℕ} {f : Frm A n}
  --   → (α : Cell A f) → Pos (η α)
  η-pos {f = ●} α = ob-pos α
  η-pos {f = f ∥ σ ▸ τ} α =
    let η-dec p = η (Inh σ p)
        lf-dec p = lf (Typ σ p) (Inh σ p)
    in nd-pos-here σ τ α η-dec lf-dec

  -- η-pos-elim : {A : 𝕆} {n : ℕ} {f : Frm A n} (α : Cell A f)
  --   → (X : (p : Pos (η α)) → Type₀)
  --   → (η-pos* : X (η-pos α))
  --   → (p : Pos (η α)) → X p
  η-pos-elim {f = ●} α X η-pos* p =
    ob-pos-elim α (λ p → X (ob-pos α) → X p)
      (λ p → p) p η-pos* 
  η-pos-elim {f = f ∥ σ ▸ τ} α X η-pos* p =
    let η-dec p = η (Inh σ p)
        lf-dec p = lf (Typ σ p) (Inh σ p)
    in nd-pos-elim σ τ α η-dec lf-dec (λ p → X (nd-pos-here σ τ α η-dec lf-dec) → X p)
         (λ x → x) (λ p q → lf-pos-elim (Typ σ p) (Inh σ p)
                            (λ q → X (nd-pos-here σ τ α η-dec lf-dec)
                                 → X (nd-pos-there σ τ α η-dec lf-dec p q)) q) p η-pos*

  -- μ : {A : 𝕆} {n : ℕ} {f : Frm A n} (σ : Tree A f)
  --   → (κ : (p : Pos σ) → Tree A (Typ σ p))
  --   → Tree A f
  μ .{f = ●} (ob α) κ = κ (ob-pos α)
  μ .{f = f ∥ (η α) ▸ α} (lf f α) κ = lf f α
  μ .{f = f ∥ (μ σ δ) ▸ τ} (nd {f = f} σ τ α δ ε) κ = 
    let w = κ (nd-pos-here σ τ α δ ε)
        κ' p q = κ (nd-pos-there σ τ α δ ε p q)
        ψ p = μ (ε p) (κ' p)
    in γ σ τ w δ ψ


  -- γ : {A : 𝕆} {n : ℕ} {f : Frm A n}
  --   → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
  --   → (ϕ : (p : Pos σ) → Tree A (Typ σ p))
  --   → (ψ : (p : Pos σ) → Tree A (Typ σ p ∥ ϕ p ▸ Inh σ p))
  --   → Tree A (f ∥ μ σ ϕ ▸ τ)
  γ .(η τ) τ (lf f .τ) ϕ ψ = ψ (η-pos τ)
  γ .(μ σ δ) τ (nd σ .τ α δ ε) ϕ ψ =
    let ϕ' p q = ϕ (μ-pos σ δ p q)
        ψ' p q = ψ (μ-pos σ δ p q)
        δ' p = μ (δ p) (ϕ' p)
        ε' p = γ (δ p) (Inh σ p) (ε p) (ϕ' p) (ψ' p)
    in nd σ τ α δ' ε'

  -- μ-pos : {A : 𝕆} {n : ℕ} {f : Frm A n} (σ : Tree A f)
  --   → (κ : (p : Pos σ) → Tree A (Typ σ p))
  --   → (p : Pos σ) (q : Pos (κ p))
  --   → Pos (μ σ κ)
  μ-pos (ob α) κ p q = ob-pos-elim α  
    (λ p → Pos (κ p) → Pos (κ (ob-pos α)))
    (λ q → q) p q  -- would be trivial given η for ob-pos
  μ-pos (lf f α) κ p q =
    lf-pos-elim f α _ p
  μ-pos (nd σ τ α δ ε) κ =
    let X p = Pos (κ p) → Pos (μ (nd σ τ α δ ε) κ)
        w = κ (nd-pos-here σ τ α δ ε)
        κ' p q = κ (nd-pos-there σ τ α δ ε p q)
        ψ p = μ (ε p) (κ' p)
    in nd-pos-elim σ τ α δ ε X (γ-pos-inl σ τ w δ ψ)
         (λ p q r → γ-pos-inr σ τ w δ ψ p
           (μ-pos (ε p) (κ' p) q r))


  -- μ-pos-fst : {A : 𝕆} {n : ℕ} {f : Frm A n} (σ : Tree A f)
  --   → (κ : (p : Pos σ) → Tree A (Typ σ p))
  --   → Pos (μ σ κ) → Pos σ
  μ-pos-fst (ob α) κ p = ob-pos α
  μ-pos-fst (lf f α) κ p = p
  μ-pos-fst (nd σ τ α δ ε) κ = 
    let w = κ (nd-pos-here σ τ α δ ε)
        κ' p q = κ (nd-pos-there σ τ α δ ε p q)
        ψ p = μ (ε p) (κ' p)
    in γ-pos-elim σ τ w δ ψ _
         (λ _ → nd-pos-here σ τ α δ ε)
         (λ p q → nd-pos-there σ τ α δ ε p
                    (μ-pos-fst (ε p) (κ' p) q))

  -- μ-pos-snd : {A : 𝕆} {n : ℕ} {f : Frm A n} (σ : Tree A f)
  --   → (κ : (p : Pos σ) → Tree A (Typ σ p))
  --   → (p : Pos (μ σ κ)) → Pos (κ (μ-pos-fst σ κ p))
  μ-pos-snd (ob α) κ p = p
  μ-pos-snd (lf f α) κ = lf-pos-elim f α _ 
  μ-pos-snd (nd σ τ α δ ε) κ = 
    let w = κ (nd-pos-here σ τ α δ ε)
        κ' p q = κ (nd-pos-there σ τ α δ ε p q)
        ψ p = μ (ε p) (κ' p)
    in γ-pos-elim σ τ w δ ψ _
         (λ p → p)
         (λ p q → μ-pos-snd (ε p) (κ' p) q)

  -- γ-pos-inl : {A : 𝕆} {n : ℕ} {f : Frm A n}
  --   → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
  --   → (ϕ : (p : Pos σ) → Tree A (Typ σ p))
  --   → (ψ : (p : Pos σ) → Tree A (Typ σ p ∥ ϕ p ▸ Inh σ p))
  --   → Pos ρ → Pos (γ σ τ ρ ϕ ψ)
  γ-pos-inl .(η τ) τ (lf f .τ) ϕ ψ = lf-pos-elim f τ _
  γ-pos-inl .(μ σ δ) τ (nd σ .τ α δ ε) ϕ ψ = 
    let ϕ' p q = ϕ (μ-pos σ δ p q)
        ψ' p q = ψ (μ-pos σ δ p q)
        δ' p = μ (δ p) (ϕ' p)
        ε' p = γ (δ p) (Inh σ p) (ε p) (ϕ' p) (ψ' p)
    in nd-pos-elim σ τ α δ ε _
         (nd-pos-here σ τ α δ' ε')
         (λ p q → nd-pos-there σ τ α δ' ε' p
                    (γ-pos-inl (δ p) (Inh σ p) (ε p) (ϕ' p) (ψ' p) q))

  -- γ-pos-inr : {A : 𝕆} {n : ℕ} {f : Frm A n}
  --   → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
  --   → (ϕ : (p : Pos σ) → Tree A (Typ σ p))
  --   → (ψ : (p : Pos σ) → Tree A (Typ σ p ∥ ϕ p ▸ Inh σ p))
  --   → (p : Pos σ) (q : Pos (ψ p))
  --   → Pos (γ σ τ ρ ϕ ψ)
  γ-pos-inr .(η τ) τ (lf f .τ) ϕ ψ p q =
    η-pos-elim τ (λ p → Pos (ψ p) → Pos (ψ (η-pos τ)))
      (λ p → p) p q
  γ-pos-inr .(μ σ δ) τ (nd σ .τ α δ ε) ϕ ψ p q = 
    let ϕ' p q = ϕ (μ-pos σ δ p q)
        ψ' p q = ψ (μ-pos σ δ p q)
        δ' p = μ (δ p) (ϕ' p)
        ε' p = γ (δ p) (Inh σ p) (ε p) (ϕ' p) (ψ' p)
        p₀ = μ-pos-fst σ δ p
        p₁ = μ-pos-snd σ δ p
    in nd-pos-there σ τ α δ' ε' p₀
         (γ-pos-inr (δ p₀) (Inh σ p₀) (ε p₀) (ϕ' p₀) (ψ' p₀) p₁ q)

  -- γ-pos-elim : {A : 𝕆} {n : ℕ} {f : Frm A n}
  --   → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
  --   → (ϕ : (p : Pos σ) → Tree A (Typ σ p))
  --   → (ψ : (p : Pos σ) → Tree A (Typ σ p ∥ ϕ p ▸ Inh σ p))
  --   → (X : Pos (γ σ τ ρ ϕ ψ) → Type₀)
  --   → (inl* : (p : Pos ρ) → X (γ-pos-inl σ τ ρ ϕ ψ p))
  --   → (inr* : (p : Pos σ) (q : Pos (ψ p)) → X (γ-pos-inr σ τ ρ ϕ ψ p q))
  --   → (p : Pos (γ σ τ ρ ϕ ψ)) → X p
  γ-pos-elim .(η τ) τ (lf f .τ) ϕ ψ X inl* inr* p = inr* (η-pos τ) p
  γ-pos-elim .(μ σ δ) τ (nd σ .τ α δ ε) ϕ ψ X inl* inr* =
    let ϕ' p q = ϕ (μ-pos σ δ p q)
        ψ' p q = ψ (μ-pos σ δ p q)
        δ' p = μ (δ p) (ϕ' p)
        ε' p = γ (δ p) (Inh σ p) (ε p) (ϕ' p) (ψ' p)
    in nd-pos-elim σ τ α δ' ε' X (inl* (nd-pos-here σ τ α δ ε))
         (λ p → γ-pos-elim (δ p) (Inh σ p) (ε p) (ϕ' p) (ψ' p)
                  (λ q → X (nd-pos-there σ τ α δ' ε' p q))
                  (λ q → inl* (nd-pos-there σ τ α δ ε p q))
                  (λ q r → inr* (μ-pos σ δ p q) r))


