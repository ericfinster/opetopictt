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

  -- μ-src : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f)
  --   → (δ : (s : Src t) → 𝕋 A (Typ t s))
  --   → (s₀ : Src t) (s₁ : Src (δ s₀))
  --   → Src (μ t δ)
  μ-src {f = ●} (ob src) δ s₀ s₁ =
    ob-src-elim src (λ s → Src (ob src)) s₀
  μ-src {f = f ∥ .(η τ) ▸ τ} (lf .f .τ) δ s₀ s₁ =
    lf-src-elim f τ (λ _ → Src (lf f τ)) s₀
  μ-src {f = f ∥ .(μ t δ) ▸ τ} (nd .τ t d δ ε) δ₁ =
    nd-src-elim τ t d δ ε (λ s → Src (δ₁ s) → Src (μ (nd τ t d δ ε) δ₁))
      (γ-src-inl t τ (δ₁ (nd-src-here τ t d δ ε)) δ (λ s₀ → μ (ε s₀) (λ s₁ → δ₁ (nd-src-there τ t d δ ε s₀ s₁))))
      (λ s₀ s₁ u → γ-src-inr t τ (δ₁ (nd-src-here τ t d δ ε)) δ
        (λ s₂ → μ (ε s₂) (λ s₃ → δ₁ (nd-src-there τ t d δ ε s₂ s₃))) s₀
        (μ-src (ε s₀) (λ s₃ → δ₁ (nd-src-there τ t d δ ε s₀ s₃)) s₁ u))

  -- μ-src-fst : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f)
  --   → (δ : (s : Src t) → 𝕋 A (Typ t s))
  --   → Src (μ t δ) → Src t
  μ-src-fst {f = ●} (ob c) δ =
    ob-src-elim c (λ _ → Src (ob c))
  μ-src-fst {f = f ∥ .(η τ) ▸ τ} (lf .f .τ) δ =
    lf-src-elim f τ (λ _ → Src (lf f τ)) 
  μ-src-fst {f = f ∥ .(μ t δ) ▸ τ} (nd .τ t d δ ε) κ =
    let w = κ (nd-src-here τ t d δ ε)
        ε' s₀ = μ (ε s₀) (λ s₁ → κ (nd-src-there τ t d δ ε s₀ s₁))
    in γ-src-elim t τ w δ ε' _
         (λ _ → nd-src-here τ t d δ ε)
         (λ s₀ s₁ → nd-src-there τ t d δ ε s₀
           (μ-src-fst (ε s₀) (λ s₂ → κ (nd-src-there τ t d δ ε s₀ s₂)) s₁))
           

  -- μ-src-snd : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f)
  --   → (δ : (s : Src t) → 𝕋 A (Typ t s))
  --   → (s : Src (μ t δ)) → Src (δ (μ-src-fst t δ s))
  μ-src-snd {f = ●} (ob c) κ =
    ob-src-elim c _
  μ-src-snd {f = f ∥ .(η τ) ▸ τ} (lf .f .τ) κ =
    lf-src-elim f τ _
  μ-src-snd {f = f ∥ .(μ t δ) ▸ τ} (nd .τ t d δ ε) κ =
    let w = κ (nd-src-here τ t d δ ε)
        ε' s₀ = μ (ε s₀) (λ s₁ → κ (nd-src-there τ t d δ ε s₀ s₁))
    in γ-src-elim t τ w δ ε' _
         (λ s → s) (λ s₀ s₁ → μ-src-snd (ε s₀) (λ s₂ → κ (nd-src-there τ t d δ ε s₀ s₂)) s₁)

  -- γ-src-inl : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f) (c : ℂ A f)
  --   → (τ : 𝕋 A (f ∥ t ▸ c))
  --   → (δ : (s : Src t) → 𝕋 A (Typ t s))
  --   → (ε : (s : Src t) → 𝕋 A (Typ t s ∥ δ s ▸ Inh t s))
  --   → Src τ → Src (γ t c τ δ ε)
  γ-src-inl {f = ●} (ob σ) c τ δ ε s = s
  γ-src-inl {f = f ∥ σ ▸ τ} .(η c) c (lf .(f ∥ σ ▸ τ) .c) δ ε =
    lf-src-elim (f ∥ σ ▸ τ) c _  
  γ-src-inl {f = f ∥ σ ▸ τ} .(μ τ₁ δ₁) c (nd .c τ₁ d δ₁ ε₁) δ ε =
    nd-src-elim c τ₁ d δ₁ ε₁ _ (nd-src-here c τ₁ d  _ _)
      (λ s₀ s₁ → nd-src-there c τ₁ d _ _ s₀
        (γ-src-inl (δ₁ s₀) (Inh τ₁ s₀) (ε₁ s₀)
                   (λ s₂ → δ (μ-src τ₁ δ₁ s₀ s₂))
                   (λ s₂ → ε (μ-src τ₁ δ₁ s₀ s₂)) s₁))

  -- γ-src-inr : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f) (c : ℂ A f)
  --   → (τ : 𝕋 A (f ∥ t ▸ c))
  --   → (δ : (s : Src t) → 𝕋 A (Typ t s))
  --   → (ε : (s : Src t) → 𝕋 A (Typ t s ∥ δ s ▸ Inh t s))
  --   → (s₀ : Src t) (s₁ : Src (ε s₀))
  --   → Src (γ t c τ δ ε)
  γ-src-inr {f = ●} (ob σ) c τ δ ε s₀ s₁ =
    ob-src-elim σ _ s₀
  γ-src-inr {f = f ∥ σ ▸ τ} .(η c) c (lf .(f ∥ σ ▸ τ) .c) δ ε =
    nd-src-elim {f = f} τ σ c
      (λ s → η (Inh σ s)) (λ s → lf (Typ σ s) (Inh σ s)) _
      (λ s → s) (λ s₀ → lf-src-elim (Typ σ s₀) (Inh σ s₀) _)
  γ-src-inr {f = f ∥ σ ▸ τ} .(μ τ₁ δ₁) c (nd .c τ₁ d δ₁ ε₁) δ ε s t =
    let s₀ = μ-src-fst τ₁ δ₁ s
        s₁ = μ-src-snd τ₁ δ₁ s
        δ'' t₀ = δ (μ-src τ₁ δ₁ s₀ t₀)
        ε'' t₀ = ε (μ-src τ₁ δ₁ s₀ t₀)
    in nd-src-there {f = f ∥ σ ▸ τ} c τ₁ d _ _ s₀
         (γ-src-inr (δ₁ s₀) (Inh τ₁ (μ-src-fst τ₁ δ₁ s)) (ε₁ s₀) δ'' ε'' s₁ t)

  -- γ-src-elim : {A : 𝕆} {n : ℕ} {f : 𝔽 A n} (t : 𝕋 A f) (c : ℂ A f)
  --   → (τ : 𝕋 A (f ∥ t ▸ c))
  --   → (δ : (s : Src t) → 𝕋 A (Typ t s))
  --   → (ε : (s : Src t) → 𝕋 A (Typ t s ∥ δ s ▸ Inh t s))
  --   → (X : Src (γ t c τ δ ε) → Type₀)
  --   → (inl* : (s : Src τ) → X (γ-src-inl t c τ δ ε s))
  --   → (inr* : (s₀ : Src t) (s₁ : Src (ε s₀)) → X (γ-src-inr t c τ δ ε s₀ s₁))
  --   → (s : Src (γ t c τ δ ε)) → X s
  γ-src-elim {f = ●} (ob σ) c τ δ ε X inl* inr* s = inl* s
  γ-src-elim {f = f ∥ σ ▸ τ₁} .(η c) c (lf .(f ∥ σ ▸ τ₁) .c) δ ε X inl* inr* s =
    inr* (nd-src-here τ₁ σ c
           (λ s₁ → η (Inh σ s₁))
           (λ s₁ → lf (Typ σ s₁) (Inh σ s₁))) s
  γ-src-elim {f = f ∥ σ ▸ τ₁} .(μ τ δ₁) c (nd .c τ d δ₁ ε₁) δ ε X inl* inr* =
    let δ'' s = μ (δ₁ s) (λ t → δ (μ-src τ δ₁ s t))
        ε'' s = γ {f = Typ τ s} (δ₁ s) (Inh τ s) (ε₁ s)
                  (λ t → δ (μ-src τ δ₁ s t)) (λ t → ε (μ-src τ δ₁ s t))
    in nd-src-elim {f = f ∥ σ ▸ τ₁} c τ d δ'' ε'' X
         (inl* (nd-src-here c τ d δ₁ ε₁))
         (λ s → γ-src-elim (δ₁ s) (Inh τ s) (ε₁ s) (λ t → δ (μ-src τ δ₁ s t)) (λ t → ε (μ-src τ δ₁ s t))
           (λ t → X (nd-src-there c τ d _ _ s t))
           (λ s' → inl* (nd-src-there c τ d δ₁ ε₁ s s'))
           (λ s' t' → inr* (μ-src τ δ₁ s s') t'))

