{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module OpetopicTypes where

  postulate

    𝕆 : Type₀

  data 𝔽 (A : 𝕆) : ℕ → Type₀
  data 𝕋 (A : 𝕆) : {n : ℕ} (f : 𝔽 A n) → Type₀

  postulate
  
    ℂ : (A : 𝕆) {n : ℕ} (f : 𝔽 A n) → Type₀
    Src : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} → 𝕋 A f → Type₀

  Typ : {A : 𝕆} {n : ℕ} {f : 𝔽 A n}
    → (t : 𝕋 A f) (s : Src t) → 𝔽 A n
    
  Inh : {A : 𝕆} {n : ℕ} {f : 𝔽 A n}
    → (t : 𝕋 A f) (s : Src t) → ℂ A (Typ t s)

  data 𝔽 (A : 𝕆) where
    ● : 𝔽 A O
    _∥_▸_ : {n : ℕ} (f : 𝔽 A n) (σ : 𝕋 A f) (τ : ℂ A f) → 𝔽 A (S n)
  
  η : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} → ℂ A f → 𝕋 A f

  μ : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f)
    → (δ : (s : Src t) → 𝕋 A (Typ t s))
    → 𝕋 A f

  γ : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f) (c : ℂ A f)
    → (τ : 𝕋 A (f ∥ t ▸ c))
    → (δ : (s : Src t) → 𝕋 A (Typ t s))
    → (ε : (s : Src t) → 𝕋 A (Typ t s ∥ δ s ▸ Inh t s))
    → 𝕋 A (f ∥ μ t δ ▸ c)

  -- These should be defined....
  postulate
  
    μ-src : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f)
      → (δ : (s : Src t) → 𝕋 A (Typ t s))
      → (s₀ : Src t) (s₁ : Src (δ s₀))
      → Src (μ t δ)

    μ-src-fst : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f)
      → (δ : (s : Src t) → 𝕋 A (Typ t s))
      → Src (μ t δ) → Src t
      
    μ-src-snd : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f)
      → (δ : (s : Src t) → 𝕋 A (Typ t s))
      → (s : Src (μ t δ)) → Src (δ (μ-src-fst t δ s))

    γ-src-inl : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f) (c : ℂ A f)
      → (τ : 𝕋 A (f ∥ t ▸ c))
      → (δ : (s : Src t) → 𝕋 A (Typ t s))
      → (ε : (s : Src t) → 𝕋 A (Typ t s ∥ δ s ▸ Inh t s))
      → Src τ → Src (γ t c τ δ ε)

    γ-src-inr : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f) (c : ℂ A f)
      → (τ : 𝕋 A (f ∥ t ▸ c))
      → (δ : (s : Src t) → 𝕋 A (Typ t s))
      → (ε : (s : Src t) → 𝕋 A (Typ t s ∥ δ s ▸ Inh t s))
      → (s₀ : Src t) (s₁ : Src (ε s₀))
      → Src (γ t c τ δ ε)
      
    γ-src-elim : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f) (c : ℂ A f)
      → (τ : 𝕋 A (f ∥ t ▸ c))
      → (δ : (s : Src t) → 𝕋 A (Typ t s))
      → (ε : (s : Src t) → 𝕋 A (Typ t s ∥ δ s ▸ Inh t s))
      → (X : Src (γ t c τ δ ε) → Type₀)
      → (inl* : (s : Src τ) → X (γ-src-inl t c τ δ ε s))
      → (inr* : (s₀ : Src t) (s₁ : Src (ε s₀)) → X (γ-src-inr t c τ δ ε s₀ s₁))
      → (s : Src (γ t c τ δ ε)) → X s

  data 𝕋 (A : 𝕆) where
    ob : ℂ A ● → 𝕋 A ●
    lf : {n : ℕ} (f : 𝔽 A n) (c : ℂ A f)
      → 𝕋 A (f ∥ η c ▸ c)
    nd : {n : ℕ} {f : 𝔽 A n} (c : ℂ A f) (t : 𝕋 A f)
      → (d : ℂ A (f ∥ t ▸ c))
      → (δ : (s : Src t) → 𝕋 A (Typ t s))
      → (ε : (s : Src t) → 𝕋 A (Typ t s ∥ δ s ▸ Inh t s))
      → 𝕋 A (f ∥ μ t δ ▸ c)

  postulate

    ob-src-elim : {A : 𝕆} (c : ℂ A ●)
      → (X : Src (ob c) → Type₀)
      → (s : Src (ob c)) → X s

    lf-src-elim : {A : 𝕆} {n : ℕ} (f : 𝔽 A n) (c : ℂ A f)
      → (X : Src (lf f c) → Type₀)
      → (s : Src (lf f c)) → X s

    nd-src-here : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} 
      → (c : ℂ A f) (t : 𝕋 A f) (d : ℂ A (f ∥ t ▸ c))
      → (δ : (s : Src t) → 𝕋 A (Typ t s))
      → (ε : (s : Src t) → 𝕋 A (Typ t s ∥ δ s ▸ Inh t s))
      → Src (nd c t d δ ε)

    nd-src-there : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} 
      → (c : ℂ A f) (t : 𝕋 A f) (d : ℂ A (f ∥ t ▸ c))
      → (δ : (s : Src t) → 𝕋 A (Typ t s))
      → (ε : (s : Src t) → 𝕋 A (Typ t s ∥ δ s ▸ Inh t s))
      → (s₀ : Src t) (s₁ : Src (ε s₀))
      → Src (nd c t d δ ε)
      
    nd-src-elim : {A : 𝕆} {n : ℕ} {f : 𝔽 A n}
      → (c : ℂ A f) (t : 𝕋 A f) (d : ℂ A (f ∥ t ▸ c))
      → (δ : (s : Src t) → 𝕋 A (Typ t s))
      → (ε : (s : Src t) → 𝕋 A (Typ t s ∥ δ s ▸ Inh t s))
      → (X : Src (nd c t d δ ε) → Type₀)
      → (hr : X (nd-src-here c t d δ ε))
      → (thr : (s₀ : Src t) (s₁ : Src (ε s₀))
           → X (nd-src-there c t d δ ε s₀ s₁))
      → (s : Src (nd c t d δ ε)) → X s

    nd-src-elim-here-β : {A : 𝕆} {n : ℕ} {f : 𝔽 A n}
      → (c : ℂ A f) (t : 𝕋 A f) (d : ℂ A (f ∥ t ▸ c))
      → (δ : (s : Src t) → 𝕋 A (Typ t s))
      → (ε : (s : Src t) → 𝕋 A (Typ t s ∥ δ s ▸ Inh t s))
      → (X : Src (nd c t d δ ε) → Type₀)
      → (hr : X (nd-src-here c t d δ ε))
      → (thr : (s₀ : Src t) (s₁ : Src (ε s₀))
           → X (nd-src-there c t d δ ε s₀ s₁))
      → nd-src-elim c t d δ ε X hr thr (nd-src-here c t d δ ε) ↦ hr
    {-# REWRITE nd-src-elim-here-β #-}

    nd-src-elim-there-β : {A : 𝕆} {n : ℕ} {f : 𝔽 A n}
      → (c : ℂ A f) (t : 𝕋 A f) (d : ℂ A (f ∥ t ▸ c))
      → (δ : (s : Src t) → 𝕋 A (Typ t s))
      → (ε : (s : Src t) → 𝕋 A (Typ t s ∥ δ s ▸ Inh t s))
      → (X : Src (nd c t d δ ε) → Type₀)
      → (hr : X (nd-src-here c t d δ ε))
      → (thr : (s₀ : Src t) (s₁ : Src (ε s₀))
           → X (nd-src-there c t d δ ε s₀ s₁))
      → (s₀ : Src t) (s₁ : Src (ε s₀))
      → nd-src-elim c t d δ ε X hr thr (nd-src-there c t d δ ε s₀ s₁) ↦ thr s₀ s₁
    {-# REWRITE nd-src-elim-there-β #-}

  --
  --  Definining source types and inhabitants
  --

  -- Typ : {A : 𝕆} {n : ℕ} {f : 𝔽 A n}
  --   → (t : 𝕋 A f) (s : Src t) → 𝔽 A n
  Typ {f = ●} (ob c) =
    ob-src-elim c (λ _ → 𝔽 _ O)
  Typ {f = f ∥ .(η τ) ▸ τ} (lf .f .τ) =
    lf-src-elim f τ (λ _ → 𝔽 _ (S _))
  Typ {f = f ∥ .(μ t δ) ▸ τ} (nd .τ t d δ ε) =
    nd-src-elim τ t d δ ε (λ _ → 𝔽 _ (S _))
      (f ∥ t ▸ τ)
      (λ s₀ s₁ → Typ (ε s₀) s₁)
  
  -- Inh : {A : 𝕆} {n : ℕ} {f : 𝔽 A n}
  --   → (t : 𝕋 A f) (s : Src t) → ℂ A (Typ t s)
  Inh {f = ●} (ob c) =
    ob-src-elim c _
  Inh {f = f ∥ .(η τ) ▸ τ} (lf .f .τ) =
    lf-src-elim f τ _
  Inh {f = f ∥ .(μ t δ) ▸ τ} (nd .τ t d δ ε) =
    let X s = ℂ _  (Typ (nd τ t d δ ε) s)
    in nd-src-elim τ t d δ ε X d (λ s₀ s₁ → Inh (ε s₀) s₁)

  postulate

    -- μ-src laws
    μ-src-fst-β : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f)
      → (δ : (s : Src t) → 𝕋 A (Typ t s))
      → (s₀ : Src t) (s₁ : Src (δ s₀))
      → μ-src-fst t δ (μ-src t δ s₀ s₁) ↦ s₀
    {-# REWRITE μ-src-fst-β #-}

    μ-src-snd-β : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f)
      → (δ : (s : Src t) → 𝕋 A (Typ t s))
      → (s₀ : Src t) (s₁ : Src (δ s₀))
      → μ-src-snd t δ (μ-src t δ s₀ s₁) ↦ s₁
    {-# REWRITE μ-src-snd-β #-}

    μ-src-η : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f)
      → (δ : (s : Src t) → 𝕋 A (Typ t s))
      → (s : Src (μ t δ))
      → μ-src t δ (μ-src-fst t δ s) (μ-src-snd t δ s) ↦ s
    {-# REWRITE μ-src-η #-}

    μ-src-typ : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f)
      → (δ : (s : Src t) → 𝕋 A (Typ t s))
      → (s : Src (μ t δ))
      → Typ (μ t δ) s ↦ Typ (δ (μ-src-fst t δ s)) (μ-src-snd t δ s)
    {-# REWRITE μ-src-typ #-}

    μ-src-inh : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f)
      → (δ : (s : Src t) → 𝕋 A (Typ t s))
      → (s : Src (μ t δ))
      → Inh (μ t δ) s ↦ Inh (δ (μ-src-fst t δ s)) (μ-src-snd t δ s)
    {-# REWRITE μ-src-inh #-}

    -- μ laws
    μ-unit-r : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f) 
      → μ t (λ s → η (Inh t s)) ↦ t
    {-# REWRITE μ-unit-r #-}

    μ-assoc : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f)
      → (δ : (s : Src t) → 𝕋 A (Typ t s))
      → (ε : (s : Src (μ t δ)) → 𝕋 A (Typ (μ t δ) s))
      → μ (μ t δ) ε ↦ μ t (λ s₀ → μ (δ s₀) (λ s₁ → ε (μ-src t δ s₀ s₁)))
    {-# REWRITE μ-assoc #-}
    
    -- γ elim rules
    γ-src-elim-inl-β : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f) (c : ℂ A f)
      → (τ : 𝕋 A (f ∥ t ▸ c))
      → (δ : (s : Src t) → 𝕋 A (Typ t s))
      → (ε : (s : Src t) → 𝕋 A (Typ t s ∥ δ s ▸ Inh t s))
      → (X : Src (γ t c τ δ ε) → Type₀)
      → (inl* : (s : Src τ) → X (γ-src-inl t c τ δ ε s))
      → (inr* : (s₀ : Src t) (s₁ : Src (ε s₀)) → X (γ-src-inr t c τ δ ε s₀ s₁))
      → (s : Src τ)
      → γ-src-elim t c τ δ ε X inl* inr* (γ-src-inl t c τ δ ε s) ↦ inl* s
    {-# REWRITE γ-src-elim-inl-β #-}

    γ-src-elim-inr-β : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f) (c : ℂ A f)
      → (τ : 𝕋 A (f ∥ t ▸ c))
      → (δ : (s : Src t) → 𝕋 A (Typ t s))
      → (ε : (s : Src t) → 𝕋 A (Typ t s ∥ δ s ▸ Inh t s))
      → (X : Src (γ t c τ δ ε) → Type₀)
      → (inl* : (s : Src τ) → X (γ-src-inl t c τ δ ε s))
      → (inr* : (s₀ : Src t) (s₁ : Src (ε s₀)) → X (γ-src-inr t c τ δ ε s₀ s₁))
      → (s₀ : Src t) (s₁ : Src (ε s₀))
      → γ-src-elim t c τ δ ε X inl* inr* (γ-src-inr t c τ δ ε s₀ s₁) ↦ inr* s₀ s₁
    {-# REWRITE γ-src-elim-inr-β #-}
    
    -- γ src laws
    γ-src-inl-typ : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f) (c : ℂ A f)
      → (τ : 𝕋 A (f ∥ t ▸ c))
      → (δ : (s : Src t) → 𝕋 A (Typ t s))
      → (ε : (s : Src t) → 𝕋 A (Typ t s ∥ δ s ▸ Inh t s))
      → (s : Src τ)
      → Typ (γ t c τ δ ε) (γ-src-inl t c τ δ ε s) ↦ Typ τ s
    {-# REWRITE γ-src-inl-typ #-}

    γ-src-inr-typ : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f) (c : ℂ A f)
      → (τ : 𝕋 A (f ∥ t ▸ c))
      → (δ : (s : Src t) → 𝕋 A (Typ t s))
      → (ε : (s : Src t) → 𝕋 A (Typ t s ∥ δ s ▸ Inh t s))
      → (s₀ : Src t) (s₁ : Src (ε s₀))
      → Typ (γ t c τ δ ε) (γ-src-inr t c τ δ ε s₀ s₁) ↦ Typ (ε s₀) s₁
    {-# REWRITE γ-src-inr-typ #-}

    -- γ laws
    γ-unit-r : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f) (c : ℂ A f)
      → (τ : 𝕋 A (f ∥ t ▸ c))
      → γ t c τ (λ s → η (Inh t s)) (λ s → lf (Typ t s) (Inh t s)) ↦ τ
    {-# REWRITE γ-unit-r #-}

  -- η : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} → ℂ A f → 𝕋 A f
  η {f = ●} c = ob c
  η {f = f ∥ σ ▸ τ} c =
    nd τ σ c (λ s → η (Inh σ s))
             (λ s → lf (Typ σ s) (Inh σ s))

  -- μ : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f)
  --   → (δ : (s : Src t) → 𝕋 A (Typ t s))
  --   → 𝕋 A f
  μ (ob c) κ = ob c
  μ (lf f c) κ = lf f c
  μ (nd c t d δ ε) κ = 
    let w = κ (nd-src-here c t d δ ε)
        ε' s₀ = μ (ε s₀) (λ s₁ → κ (nd-src-there c t d δ ε s₀ s₁))
    in γ t c w δ ε'

  -- γ : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f) (c : ℂ A f)
  --   → (τ : 𝕋 A (f ∥ t ▸ c))
  --   → (δ : (s : Src t) → 𝕋 A (Typ t s))
  --   → (ε : (s : Src t) → 𝕋 A (Typ t s ∥ δ s ▸ Inh t s))
  --   → 𝕋 A (f ∥ μ t δ ▸ c)
  γ {f = ●} (ob src) tgt arr ϕ ψ = arr
  γ {f = f ∥ σ₀ ▸ τ₀} .(η c) c (lf .(f ∥ σ₀ ▸ τ₀) .c) ϕ ψ =
    ψ (nd-src-here τ₀ σ₀ c (λ s₀ → η (Inh σ₀ s₀)) (λ s₀ → lf (Typ σ₀ s₀) (Inh σ₀ s₀)))
  γ {f = f ∥ σ₀ ▸ τ₀} .(μ τ δ) c (nd .c τ d δ ε) ϕ ψ =
    let δ' s₀ = μ (δ s₀) (λ s₁ → ϕ (μ-src τ δ s₀ s₁))
        ε' s₀ = γ {f = Typ τ s₀} (δ s₀) (Inh τ s₀) (ε s₀)
                  (λ s₁ → ϕ (μ-src τ δ s₀ s₁))
                  (λ s₁ → ψ (μ-src τ δ s₀ s₁))
    in nd c τ d δ' ε'
