{-# OPTIONS --without-K --rewriting #-}

module OpetopicTT where

  𝕌 = Set

  record ⊤ : 𝕌 where
    constructor tt
    
  data ⊥ : 𝕌 where
  
  record Σ (A : 𝕌) (B : A → 𝕌) : 𝕌 where
    constructor _,_
    field
      fst : A
      snd : B fst

  data _⊔_ (A : 𝕌) (B : 𝕌) : 𝕌 where
    inl : A → A ⊔ B
    inr : B → A ⊔ B

  infix 30 _↦_
  postulate  -- HIT
    _↦_ : ∀ {i} {A : Set i} → A → A → Set i

  {-# BUILTIN REWRITE _↦_ #-}

  data Frm (A : 𝕌) : 𝕌
  data Tree (A : 𝕌) : Frm A → 𝕌

  postulate
  
    Cell : (A : 𝕌) (f : Frm A) → 𝕌

  data Frm (A : 𝕌) where
    ● : Frm A
    _∥_▸_ : (f : Frm A) (σ : Tree A f) (τ : Cell A f) → Frm A

  Pos : {A : 𝕌} (f : Frm A) → Tree A f → 𝕌
  Typ : {A : 𝕌} (f : Frm A) (σ : Tree A f) (p : Pos f σ) → Frm A
  Inh : {A : 𝕌} (f : Frm A) (σ : Tree A f) (p : Pos f σ) → Cell A (Typ f σ p)

  {-# TERMINATING #-}
  η : {A : 𝕌} (f : Frm A) → Cell A f → Tree A f

  μ : {A : 𝕌} (f : Frm A) (σ : Tree A f)
    → (κ : (p : Pos f σ) → Tree A (Typ f σ p))
    → Tree A f

  γ : {A : 𝕌} (f : Frm A)
    → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
    → (ϕ : (p : Pos f σ) → Tree A (Typ f σ p))
    → (ψ : (p : Pos f σ) → Tree A (Typ f σ p ∥ ϕ p ▸ Inh f σ p))
    → Tree A (f ∥ μ f σ ϕ ▸ τ)

  data Tree (A : 𝕌) where
    ob : (α : Cell A ●) → Tree A ●
    lf : (f : Frm A) (α : Cell A f)
      → Tree A (f ∥ η f α ▸ α)
    nd : (f : Frm A) 
      → (σ : Tree A f) (τ : Cell A f)  (α : Cell A (f ∥ σ ▸ τ))
      → (δ : (p : Pos f σ) → Tree A (Typ f σ p))
      → (ε : (p : Pos f σ) → Tree A (Typ f σ p ∥ δ p ▸ Inh f σ p))
      → Tree A (f ∥ μ f σ δ ▸ τ)

  --
  --  Positions, their types and inhabitants
  --

  -- Pos : {A : 𝕌} (f : Frm A) → Tree A f → 𝕌
  Pos .● (ob α) = ⊤
  Pos ._ (lf f α) = ⊥
  Pos ._ (nd f σ τ α δ ε) = ⊤ ⊔ Σ (Pos f σ) (λ p → Pos (Typ f σ p ∥ δ p ▸ Inh f σ p) (ε p))

  -- Typ : {A : 𝕌} (f : Frm A) (σ : Tree A f) (p : Pos f σ) → Frm A
  Typ .● (ob α) tt = ●
  Typ ._ (lf f α) ()
  Typ ._ (nd f σ τ α δ ε) (inl tt) = f ∥ σ ▸ τ
  Typ ._ (nd f σ τ α δ ε) (inr (p , q)) =
    Typ (Typ f σ p ∥ δ p ▸ Inh f σ p) (ε p) q

  -- Inh : {A : 𝕌} (f : Frm A) (σ : Tree A f) (p : Pos f σ) → Cell A (Typ f σ p)
  Inh .● (ob α) tt = α
  Inh ._ (lf f α) ()
  Inh ._ (nd f σ τ α δ ε) (inl tt) = α
  Inh ._ (nd f σ τ α δ ε) (inr (p , q)) =
    Inh (Typ f σ p ∥ δ p ▸ Inh f σ p) (ε p) q

  postulate
  
    η-pos : {A : 𝕌} (f : Frm A)
      → (α : Cell A f) → Pos f (η f α)

    η-pos-elim : {A : 𝕌} (f : Frm A) (α : Cell A f)
      → (X : (p : Pos f (η f α)) → 𝕌)
      → (η-pos* : X (η-pos f α))
      → (p : Pos f (η f α)) → X p

    μ-pos : {A : 𝕌} (f : Frm A) (σ : Tree A f)
      → (κ : (p : Pos f σ) → Tree A (Typ f σ p))
      → (p : Pos f σ) (q : Pos (Typ f σ p) (κ p))
      → Pos f (μ f σ κ)

    μ-pos-fst : {A : 𝕌} (f : Frm A) (σ : Tree A f)
      → (κ : (p : Pos f σ) → Tree A (Typ f σ p))
      → Pos f (μ f σ κ) → Pos f σ

    μ-pos-snd : {A : 𝕌} (f : Frm A) (σ : Tree A f)
      → (κ : (p : Pos f σ) → Tree A (Typ f σ p))
      → (p : Pos f (μ f σ κ)) → Pos (Typ f σ (μ-pos-fst f σ κ p)) (κ (μ-pos-fst f σ κ p))

    γ-pos-inl : {A : 𝕌} (f : Frm A)
      → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
      → (ϕ : (p : Pos f σ) → Tree A (Typ f σ p))
      → (ψ : (p : Pos f σ) → Tree A (Typ f σ p ∥ ϕ p ▸ Inh f σ p))
      → Pos (f ∥ σ ▸ τ) ρ → Pos (f ∥ μ f σ ϕ ▸ τ) (γ f σ τ ρ ϕ ψ)

    γ-pos-inr : {A : 𝕌} (f : Frm A)
      → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
      → (ϕ : (p : Pos f σ) → Tree A (Typ f σ p))
      → (ψ : (p : Pos f σ) → Tree A (Typ f σ p ∥ ϕ p ▸ Inh f σ p))
      → (p : Pos f σ) (q : Pos (Typ f σ p ∥ ϕ p ▸ Inh f σ p) (ψ p))
      → Pos (f ∥ μ f σ ϕ ▸ τ) (γ f σ τ ρ ϕ ψ)

    γ-pos-elim : {A : 𝕌} (f : Frm A)
      → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
      → (ϕ : (p : Pos f σ) → Tree A (Typ f σ p))
      → (ψ : (p : Pos f σ) → Tree A (Typ f σ p ∥ ϕ p ▸ Inh f σ p))
      → (X : Pos (f ∥ μ f σ ϕ ▸ τ) (γ f σ τ ρ ϕ ψ) → 𝕌)
      → (inl* : (p : Pos (f ∥ σ ▸ τ) ρ) → X (γ-pos-inl f σ τ ρ ϕ ψ p))
      → (inr* : (p : Pos f σ) (q : Pos (Typ f σ p ∥ ϕ p ▸ Inh f σ p) (ψ p)) → X (γ-pos-inr f σ τ ρ ϕ ψ p q))
      → (p : Pos (f ∥ μ f σ ϕ ▸ τ) (γ f σ τ ρ ϕ ψ)) → X p


  postulate

    -- η-pos laws
    η-pos-typ : {A : 𝕌} (f : Frm A)
      → (α : Cell A f) (p : Pos f (η f α))
      → Typ f (η f α) p ↦ f
    {-# REWRITE η-pos-typ #-}

    η-pos-inh : {A : 𝕌} (f : Frm A)
      → (α : Cell A f) (p : Pos f (η f α))
      → Inh f (η f α) (η-pos f α) ↦ α
    {-# REWRITE η-pos-inh #-}

  --   η-pos-elim-β : {A : 𝕌} (f : Frm A) (α : Cell A f)
  --     → (X : (p : Pos f (η f α)) → Type₀)
  --     → (η-pos* : X (η-pos f α))
  --     → η-pos-elim f α X η-pos* (η-pos f α) ↦ η-pos*
  --   {-# REWRITE η-pos-elim-β #-}
    
    -- μ-pos laws
    μ-pos-typ : {A : 𝕌} (f : Frm A) (σ : Tree A f)
      → (κ : (p : Pos f σ) → Tree A (Typ f σ p))
      → (p : Pos f (μ f σ κ))
      → Typ f (μ f σ κ) p ↦ Typ (Typ f σ (μ-pos-fst f σ κ p)) (κ (μ-pos-fst f σ κ p)) (μ-pos-snd f σ κ p)
    {-# REWRITE μ-pos-typ #-}

    μ-pos-inh : {A : 𝕌} (f : Frm A) (σ : Tree A f)
      → (κ : (p : Pos f σ) → Tree A (Typ f σ p))
      → (p : Pos f (μ f σ κ))
      → Inh f (μ f σ κ) p ↦ Inh (Typ f σ (μ-pos-fst f σ κ p)) (κ (μ-pos-fst f σ κ p)) (μ-pos-snd f σ κ p)
    {-# REWRITE μ-pos-inh #-}
    
    μ-pos-fst-β : {A : 𝕌} (f : Frm A) (σ : Tree A f)
      → (κ : (p : Pos f σ) → Tree A (Typ f σ p))
      → (p : Pos f σ) (q : Pos (Typ f σ p) (κ p))
      → μ-pos-fst f σ κ (μ-pos f σ κ p q) ↦ p
    {-# REWRITE μ-pos-fst-β #-}

    μ-pos-snd-β : {A : 𝕌} (f : Frm A) (σ : Tree A f)
      → (κ : (p : Pos f σ) → Tree A (Typ f σ p))
      → (p : Pos f σ) (q : Pos (Typ f σ p) (κ p))
      → μ-pos-snd f σ κ (μ-pos f σ κ p q) ↦ q
    {-# REWRITE μ-pos-snd-β #-}

    μ-pos-η : {A : 𝕌} (f : Frm A) (σ : Tree A f)
      → (κ : (p : Pos f σ) → Tree A (Typ f σ p))
      → (p : Pos f (μ f σ κ))
      → μ-pos f σ κ (μ-pos-fst f σ κ p) (μ-pos-snd f σ κ p) ↦ p
    {-# REWRITE μ-pos-η #-}

    -- μ laws
    μ-unit-r : {A : 𝕌} (f : Frm A) (σ : Tree A f) 
      → μ f σ (λ p → η (Typ f σ p) (Inh f σ p)) ↦ σ
    {-# REWRITE μ-unit-r #-}

    μ-unit-l : {A : 𝕌} (f : Frm A)
      → (α : Cell A f) (κ : (p : Pos f (η f α)) → Tree A (Typ f (η f α) p))
      → μ f (η f α) κ ↦ κ (η-pos f α)
    {-# REWRITE μ-unit-l #-}

    μ-assoc : {A : 𝕌} (f : Frm A) (σ : Tree A f)
      → (κ : (p : Pos f σ) → Tree A (Typ f σ p))
      → (θ : (p : Pos f (μ f σ κ)) → Tree A (Typ f (μ f σ κ) p))
      → μ f (μ f σ κ) θ ↦ μ f σ (λ p → μ (Typ f σ p) (κ p) (λ q → θ (μ-pos f σ κ p q)))
    {-# REWRITE μ-assoc #-}
    
  --   -- γ elim comp rules
  --   γ-pos-elim-inl-β : {A : 𝕌} (f : Frm A)
  --     → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
  --     → (ϕ : (p : Pos f σ) → Tree A (Typ f σ p))
  --     → (ψ : (p : Pos f σ) → Tree A (Typ f σ p ∥ ϕ p ▸ Inh f σ p))
  --     → (X : Pos (f ∥ μ f σ ϕ ▸ τ) (γ f σ τ ρ ϕ ψ) → Type₀)
  --     → (inl* : (p : Pos (f ∥ σ ▸ τ) ρ) → X (γ-pos-inl f σ τ ρ ϕ ψ p))
  --     → (inr* : (p : Pos f σ) (q : Pos (Typ f σ p ∥ ϕ p ▸ Inh f σ p) (ψ p)) → X (γ-pos-inr f σ τ ρ ϕ ψ p q))
  --     → (p : Pos (f ∥ σ ▸ τ) ρ)
  --     → γ-pos-elim f σ τ ρ ϕ ψ X inl* inr* (γ-pos-inl f σ τ ρ ϕ ψ p) ↦ inl* p
  --   {-# REWRITE γ-pos-elim-inl-β #-}

  --   γ-pos-elim-inr-β : {A : 𝕌} (f : Frm A)
  --     → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
  --     → (ϕ : (p : Pos f σ) → Tree A (Typ f σ p))
  --     → (ψ : (p : Pos f σ) → Tree A (Typ f σ p ∥ ϕ p ▸ Inh f σ p))
  --     → (X : Pos (f ∥ μ f σ ϕ ▸ τ) (γ f σ τ ρ ϕ ψ) → Type₀)
  --     → (inl* : (p : Pos (f ∥ σ ▸ τ) ρ) → X (γ-pos-inl f σ τ ρ ϕ ψ p))
  --     → (inr* : (p : Pos f σ) (q : Pos (Typ f σ p ∥ ϕ p ▸ Inh f σ p) (ψ p)) → X (γ-pos-inr f σ τ ρ ϕ ψ p q))
  --     → (p : Pos f σ) (q : Pos (Typ f σ p ∥ ϕ p ▸ Inh f σ p) (ψ p))
  --     → γ-pos-elim f σ τ ρ ϕ ψ X inl* inr* (γ-pos-inr f σ τ ρ ϕ ψ p q) ↦ inr* p q
  --   {-# REWRITE γ-pos-elim-inr-β #-}
    
  --   -- γ pos laws
  --   γ-pos-typ : {A : 𝕌} (f : Frm A)
  --     → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
  --     → (ϕ : (p : Pos f σ) → Tree A (Typ f σ p))
  --     → (ψ : (p : Pos f σ) → Tree A (Typ f σ p ∥ ϕ p ▸ Inh f σ p))
  --     → (p : Pos (f ∥ μ f σ ϕ ▸ τ) (γ f σ τ ρ ϕ ψ))
  --     → Typ (f ∥ μ f σ ϕ ▸ τ) (γ f σ τ ρ ϕ ψ) p ↦
  --         γ-pos-elim f σ τ ρ ϕ ψ (λ _ → Frm A (S n))
  --                    (λ p → Typ (f ∥ σ ▸ τ) ρ p)
  --                    (λ p q → Typ (Typ f σ p ∥ ϕ p ▸ Inh f σ p) (ψ p) q) p
  --   {-# REWRITE γ-pos-typ #-}

  --   γ-pos-inh : {A : 𝕌} (f : Frm A)
  --     → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
  --     → (ϕ : (p : Pos f σ) → Tree A (Typ f σ p))
  --     → (ψ : (p : Pos f σ) → Tree A (Typ f σ p ∥ ϕ p ▸ Inh f σ p))
  --     → (p : Pos (f ∥ μ f σ ϕ ▸ τ) (γ f σ τ ρ ϕ ψ))
  --     → Inh (f ∥ μ f σ ϕ ▸ τ) (γ f σ τ ρ ϕ ψ) p ↦
  --         γ-pos-elim f σ τ ρ ϕ ψ (λ p → Cell A (Typ (f ∥ μ f σ ϕ ▸ τ) (γ f σ τ ρ ϕ ψ) p))
  --           (λ p → Inh (f ∥ σ ▸ τ) ρ p)
  --           (λ p q → Inh (Typ f σ p ∥ ϕ p ▸ Inh f σ p) (ψ p) q) p
  --   {-# REWRITE γ-pos-inh #-}

  --   -- γ laws
  --   γ-unit-r : {A : 𝕌} (f : Frm A)
  --     → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
  --     → γ f σ τ ρ (λ p → η (Typ f σ p) (Inh f σ p)) (λ p → lf (Typ f σ p) (Inh f σ p)) ↦ ρ
  --   {-# REWRITE γ-unit-r #-}

  --   -- Doesn't seem to be necessary for typechecking below, but ...
  --   γ-assoc : {A : 𝕌} (f : Frm A)
  --     → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
  --     → (ϕ₀ : (p : Pos f σ) → Tree A (Typ f σ p))
  --     → (ψ₀ : (p : Pos f σ) → Tree A (Typ f σ p ∥ ϕ₀ p ▸ Inh f σ p))
  --     → (ϕ₁ : (p : Pos f (μ f σ ϕ₀)) → Tree A (Typ f (μ f σ ϕ₀) p))
  --     → (ψ₁ : (p : Pos f (μ f σ ϕ₀)) → Tree A (Typ f (μ f σ ϕ₀) p ∥ ϕ₁ p ▸ Inh f (μ f σ ϕ₀) p))
  --     → γ f (μ f σ ϕ₀) τ (γ f σ τ ρ ϕ₀ ψ₀) ϕ₁ ψ₁ ↦
  --       γ f σ τ ρ (λ p → μ (Typ f σ p) (ϕ₀ p) (λ q → ϕ₁ (μ-pos f σ ϕ₀ p q)))
  --               (λ p → γ (Typ f σ p) (ϕ₀ p) (Inh f σ p) (ψ₀ p)
  --                        (λ q → ϕ₁ (μ-pos f σ ϕ₀ p q))
  --                        (λ q → ψ₁ (μ-pos f σ ϕ₀ p q)))

  --   -- Finally, it seems there should be the interchange law
  --   -- Is this sufficient?
  --   γμ-ichg : {A : 𝕌} (f : Frm A)
  --     → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
  --     → (ϕ : (p : Pos f σ) → Tree A (Typ f σ p))
  --     → (ψ : (p : Pos f σ) → Tree A (Typ f σ p ∥ ϕ p ▸ Inh f σ p))
  --     → (κ : (p : Pos (f ∥ σ ▸ τ) ρ) → Tree A (Typ (f ∥ σ ▸ τ) ρ p))
  --     → γ f σ τ (μ (f ∥ σ ▸ τ) ρ κ) ϕ ψ ↦
  --       μ (f ∥ μ f σ ϕ ▸ τ) (γ f σ τ ρ ϕ ψ)
  --         (γ-pos-elim f σ τ ρ ϕ ψ
  --           (λ p → Tree A (Typ (f ∥ μ f σ ϕ ▸ τ) (γ f σ τ ρ ϕ ψ) p)) κ
  --           (λ p q → η ((Typ (Typ f σ p ∥ ϕ p ▸ Inh f σ p) (ψ p) q)) (Inh (Typ f σ p ∥ ϕ p ▸ Inh f σ p) (ψ p) q)))


  -- η : {A : 𝕌} (f : Frm A) → Cell A f → Tree A f
  η ● α = ob α
  η (f ∥ σ ▸ τ) α =
    let η-dec p = η (Typ f σ p) (Inh f σ p)
        lf-dec p = lf (Typ f σ p) (Inh f σ p)
    in nd f σ τ α η-dec lf-dec

  -- μ : {A : 𝕌} (f : Frm A) (σ : Tree A f)
  --   → (κ : (p : Pos f σ) → Tree A (Typ f σ p))
  --   → Tree A f
  μ .● (ob α) κ = κ tt
  μ ._ (lf f α) κ = lf f α
  μ ._ (nd f σ τ α δ ε) κ = 
    let w = κ (inl tt)
        κ' p q = κ (inr (p , q))
        ψ p = μ (Typ f σ p ∥ δ p ▸ Inh f σ p) (ε p) (κ' p)
    in γ f σ τ w δ ψ

  -- γ : {A : 𝕌} (f : Frm A)
  --   → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
  --   → (ϕ : (p : Pos f σ) → Tree A (Typ f σ p))
  --   → (ψ : (p : Pos f σ) → Tree A (Typ f σ p ∥ ϕ p ▸ Inh f σ p))
  --   → Tree A (f ∥ μ f σ ϕ ▸ τ)
  γ f .(η f τ) τ (lf .f .τ) ϕ ψ = ψ (η-pos f τ)
  γ f .(μ f σ δ) τ (nd .f σ .τ α δ ε) ϕ ψ = 
    let ϕ' p q = ϕ (μ-pos f σ δ p q)
        ψ' p q = ψ (μ-pos f σ δ p q)
        δ' p = μ (Typ f σ p) (δ p) (ϕ' p)
        ε' p = γ (Typ f σ p) (δ p) (Inh f σ p) (ε p) (ϕ' p) (ψ' p)
    in nd f σ τ α δ' ε' 

  -- -- η-pos : {A : 𝕌} (f : Frm A)
  -- --   → (α : Cell A f) → Pos f (η f α)
  -- η-pos ● α = ob-pos α
  -- η-pos (f ∥ σ ▸ τ) α =
  --   let η-dec p = η (Typ f σ p) (Inh f σ p)
  --       lf-dec p = lf (Typ f σ p) (Inh f σ p)
  --   in nd-pos-here f σ τ α η-dec lf-dec

  -- -- η-pos-elim : {A : 𝕌} (f : Frm A) (α : Cell A f)
  -- --   → (X : (p : Pos f (η f α)) → Type₀)
  -- --   → (η-pos* : X (η-pos α))
  -- --   → (p : Pos f (η f α)) → X p
  -- η-pos-elim ● α X η-pos* p =
  --   ob-pos-elim α (λ p → X (ob-pos α) → X p)
  --     (λ p → p) p η-pos* 
  -- η-pos-elim (f ∥ σ ▸ τ) α X η-pos* p =
  --   let η-dec p = η (Typ f σ p) (Inh f σ p)
  --       lf-dec p = lf (Typ f σ p) (Inh f σ p)
  --   in nd-pos-elim f σ τ α η-dec lf-dec (λ p → X (nd-pos-here f σ τ α η-dec lf-dec) → X p)
  --        (λ x → x) (λ p q → lf-pos-elim (Typ f σ p) (Inh f σ p)
  --                           (λ q → X (nd-pos-here f σ τ α η-dec lf-dec)
  --                                → X (nd-pos-there f σ τ α η-dec lf-dec p q)) q) p η-pos*

  -- -- μ-pos : {A : 𝕌} (f : Frm A) (σ : Tree A f)
  -- --   → (κ : (p : Pos f σ) → Tree A (Typ f σ p))
  -- --   → (p : Pos f σ) (q : Pos (Typ f σ p) (κ p))
  -- --   → Pos f (μ f σ κ)
  -- μ-pos _ (ob α) κ p q =
  --   let X p = Pos ● (κ p) → Pos ● (κ (ob-pos α))
  --   in ob-pos-elim α X (λ q → q) p q  -- would be trivial given η for ob-pos
  -- μ-pos _ (lf f α) κ p q =
  --   let X _ = Pos (f ∥ η f α ▸ α) (lf f α)
  --   in lf-pos-elim f α X p 
  -- μ-pos _ (nd f σ τ α δ ε) κ =
  --   let X p = Pos (Typ (f ∥ μ f σ δ ▸ τ) (nd f σ τ α δ ε) p) (κ p)
  --             → Pos (f ∥ μ f σ δ ▸ τ) (μ (f ∥ μ f σ δ ▸ τ) (nd f σ τ α δ ε) κ)
  --       w = κ (nd-pos-here f σ τ α δ ε)
  --       κ' p q = κ (nd-pos-there f σ τ α δ ε p q)
  --       ψ p = μ (Typ f σ p ∥ δ p ▸ Inh f σ p) (ε p) (κ' p)
  --   in nd-pos-elim f σ τ α δ ε X (γ-pos-inl f σ τ w δ ψ) 
  --        (λ p q r → γ-pos-inr f σ τ w δ ψ p
  --          (μ-pos (Typ f σ p ∥ δ p ▸ Inh f σ p) (ε p) (κ' p) q r))


  -- -- μ-pos-fst : {A : 𝕌} (f : Frm A) (σ : Tree A f)
  -- --   → (κ : (p : Pos f σ) → Tree A (Typ f σ p))
  -- --   → Pos f (μ f σ κ) → Pos f σ
  -- μ-pos-fst .● (ob α) κ p = ob-pos α
  -- μ-pos-fst .(f ∥ η f α ▸ α) (lf f α) κ p = p
  -- μ-pos-fst .(f ∥ μ f σ δ ▸ τ) (nd f σ τ α δ ε) κ = 
  --   let w = κ (nd-pos-here f σ τ α δ ε)
  --       κ' p q = κ (nd-pos-there f σ τ α δ ε p q)
  --       ψ p = μ (Typ f σ p ∥ δ p ▸ Inh f σ p) (ε p) (κ' p)
  --   in γ-pos-elim f σ τ w δ ψ _
  --        (λ _ → nd-pos-here f σ τ α δ ε)
  --        (λ p q → nd-pos-there f σ τ α δ ε p
  --                   (μ-pos-fst (Typ f σ p ∥ δ p ▸ Inh f σ p) (ε p) (κ' p) q))

  -- -- μ-pos-snd : {A : 𝕌} (f : Frm A) (σ : Tree A f)
  -- --   → (κ : (p : Pos f σ) → Tree A (Typ f σ p))
  -- --   → (p : Pos f (μ f σ κ)) → Pos (κ (μ-pos-fst f σ κ p))
  -- μ-pos-snd .● (ob α) κ p = p
  -- μ-pos-snd .(f ∥ η f α ▸ α) (lf f α) κ = lf-pos-elim f α _ 
  -- μ-pos-snd .(f ∥ μ f σ δ ▸ τ) (nd f σ τ α δ ε) κ = 
  --   let w = κ (nd-pos-here f σ τ α δ ε)
  --       κ' p q = κ (nd-pos-there f σ τ α δ ε p q)
  --       ψ p = μ (Typ f σ p ∥ δ p ▸ Inh f σ p) (ε p) (κ' p)
  --   in γ-pos-elim f σ τ w δ ψ _
  --        (λ p → p)
  --        (λ p q → μ-pos-snd (Typ f σ p ∥ δ p ▸ Inh f σ p) (ε p) (κ' p) q)

  -- -- γ-pos-inl : {A : 𝕌} (f : Frm A)
  -- --   → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
  -- --   → (ϕ : (p : Pos f σ) → Tree A (Typ f σ p))
  -- --   → (ψ : (p : Pos f σ) → Tree A (Typ f σ p ∥ ϕ p ▸ Inh f σ p))
  -- --   → Pos (f ∥ σ ▸ τ) ρ → Pos (f ∥ μ f σ ϕ ▸ τ) (γ f σ τ ρ ϕ ψ)
  -- γ-pos-inl .f .(η f α) .α (lf f α) ϕ ψ = lf-pos-elim f α _
  -- γ-pos-inl .f .(μ f σ δ) .τ (nd f σ τ α δ ε) ϕ ψ = 
  --   let ϕ' p q = ϕ (μ-pos f σ δ p q)
  --       ψ' p q = ψ (μ-pos f σ δ p q)
  --       δ' p = μ (Typ f σ p) (δ p) (ϕ' p)
  --       ε' p = γ (Typ f σ p) (δ p) (Inh f σ p) (ε p) (ϕ' p) (ψ' p)
  --   in nd-pos-elim f σ τ α δ ε _
  --        (nd-pos-here f σ τ α δ' ε')
  --        (λ p q → nd-pos-there f σ τ α δ' ε' p
  --                   (γ-pos-inl (Typ f σ p) (δ p) (Inh f σ p) (ε p) (ϕ' p) (ψ' p) q))

  -- -- γ-pos-inr : {A : 𝕌} (f : Frm A)
  -- --   → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
  -- --   → (ϕ : (p : Pos f σ) → Tree A (Typ f σ p))
  -- --   → (ψ : (p : Pos f σ) → Tree A (Typ f σ p ∥ ϕ p ▸ Inh f σ p))
  -- --   → (p : Pos f σ) (q : Pos (ψ p))
  -- --   → Pos (f ∥ μ f σ ϕ ▸ τ) (γ f σ τ ρ ϕ ψ)
  -- γ-pos-inr .f .(η f α) .α (lf f α) ϕ ψ p q =
  --   η-pos-elim f α (λ p → Pos (f ∥ ϕ p ▸ Inh f (η f α) p) (ψ p) → Pos (f ∥ ϕ (η-pos f α) ▸ α) (ψ (η-pos f α)))
  --     (λ p → p) p q
  -- γ-pos-inr .f .(μ f σ δ) .τ (nd f σ τ α δ ε) ϕ ψ p q = 
  --   let ϕ' p q = ϕ (μ-pos f σ δ p q)
  --       ψ' p q = ψ (μ-pos f σ δ p q)
  --       δ' p = μ (Typ f σ p) (δ p) (ϕ' p)
  --       ε' p = γ (Typ f σ p) (δ p) (Inh f σ p) (ε p) (ϕ' p) (ψ' p)
  --       p₀ = μ-pos-fst f σ δ p
  --       p₁ = μ-pos-snd f σ δ p
  --   in nd-pos-there f σ τ α δ' ε' p₀
  --        (γ-pos-inr (Typ f σ p₀) (δ p₀) (Inh f σ p₀) (ε p₀) (ϕ' p₀) (ψ' p₀) p₁ q)

  -- -- γ-pos-elim : {A : 𝕌} (f : Frm A)
  -- --   → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
  -- --   → (ϕ : (p : Pos f σ) → Tree A (Typ f σ p))
  -- --   → (ψ : (p : Pos f σ) → Tree A (Typ f σ p ∥ ϕ p ▸ Inh f σ p))
  -- --   → (X : Pos (f ∥ μ f σ ϕ ▸ τ) (γ f σ τ ρ ϕ ψ) → Type₀)
  -- --   → (inl* : (p : Pos (f ∥ σ ▸ τ) ρ) → X (γ-pos-inl f σ τ ρ ϕ ψ p))
  -- --   → (inr* : (p : Pos f σ) (q : Pos (ψ p)) → X (γ-pos-inr f σ τ ρ ϕ ψ p q))
  -- --   → (p : Pos (f ∥ μ f σ ϕ ▸ τ) (γ f σ τ ρ ϕ ψ)) → X p
  -- γ-pos-elim .f .(η f α) .α (lf f α) ϕ ψ X inl* inr* p = inr* (η-pos f α) p
  -- γ-pos-elim .f .(μ f σ δ) .τ (nd f σ τ α δ ε) ϕ ψ X inl* inr* =
  --   let ϕ' p q = ϕ (μ-pos f σ δ p q)
  --       ψ' p q = ψ (μ-pos f σ δ p q)
  --       δ' p = μ (Typ f σ p) (δ p) (ϕ' p)
  --       ε' p = γ (Typ f σ p) (δ p) (Inh f σ p) (ε p) (ϕ' p) (ψ' p)
  --   in nd-pos-elim f σ τ α δ' ε' X (inl* (nd-pos-here f σ τ α δ ε))
  --        (λ p → γ-pos-elim (Typ f σ p) (δ p) (Inh f σ p) (ε p) (ϕ' p) (ψ' p)
  --                 (λ q → X (nd-pos-there f σ τ α δ' ε' p q))
  --                 (λ q → inl* (nd-pos-there f σ τ α δ ε p q))
  --                 (λ q r → inr* (μ-pos f σ δ p q) r))


