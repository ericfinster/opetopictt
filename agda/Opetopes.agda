{-# OPTIONS --without-K --rewriting --no-positivity-check #-}

open import Base

module Opetopes where

  data 𝔽 : ℕ → 𝕌
  data 𝕆 : {n : ℕ} (f : 𝔽 n) → 𝕌
  data Pos : {n : ℕ} {f : 𝔽 n} → 𝕆 f → 𝕌 
  data Face : {n : ℕ} → 𝔽 n → 𝕌

  infixl 40 _▸_
  
  data 𝔽 where
    ● : 𝔽 O
    _▸_ : {n : ℕ} (f : 𝔽 n) → 𝕆 f → 𝔽 (S n)

  Typ : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f) (s : Pos o) → 𝔽 n

  η : {n : ℕ} (f : 𝔽 n) → 𝕆 f

  η-pos : {n : ℕ} (f : 𝔽 n)
    → Pos (η f)

  η-pos-elim : {n : ℕ} (f : 𝔽 n)
    → (X : (p : Pos (η f)) → 𝕌)
    → (η-pos* : X (η-pos f))
    → (p : Pos (η f)) → X p

  μ : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
    → (κ : (s : Pos o) → 𝕆 (Typ o s))
    → 𝕆 f

  μ-pos : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
    → (κ : (s : Pos o) → 𝕆 (Typ o s))
    → (s : Pos o) (t : Pos (κ s))
    → Pos (μ o κ)

  μ-pos-fst : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
    → (κ : (s : Pos o) → 𝕆 (Typ o s))
    → Pos (μ o κ) → Pos o

  μ-pos-snd : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
    → (κ : (s : Pos o) → 𝕆 (Typ o s))
    → (s : Pos (μ o κ)) → Pos (κ (μ-pos-fst o κ s))

  γ : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
    → (δ : (s : Pos o) → 𝕆 (Typ o s))
    → (ε : (s : Pos o) → 𝕆 (Typ o s ▸ δ s))
    → 𝕆 (f ▸ μ o δ)

  γ-pos-inl : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
    → (δ : (s : Pos o) → 𝕆 (Typ o s))
    → (ε : (s : Pos o) → 𝕆 (Typ o s ▸ δ s))
    → Pos p → Pos (γ f o p δ ε)

  γ-pos-inr : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
    → (δ : (s : Pos o) → 𝕆 (Typ o s))
    → (ε : (s : Pos o) → 𝕆 (Typ o s ▸ δ s))
    → (s : Pos o) (t : Pos (ε s))
    → Pos (γ f o p δ ε)

  γ-pos-elim : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
    → (δ : (s : Pos o) → 𝕆 (Typ o s))
    → (ε : (s : Pos o) → 𝕆 (Typ o s ▸ δ s))
    → (X : Pos (γ f o p δ ε) → 𝕌)
    → (left : (s : Pos p) → X (γ-pos-inl f o p δ ε s))
    → (right : (s : Pos o) (t : Pos (ε s)) → X (γ-pos-inr f o p δ ε s t))
    → (s : Pos (γ f o p δ ε)) → X s

  data 𝕆 where
    ob : 𝕆 ●
    lf : {n : ℕ} (f : 𝔽 n) → 𝕆 (f ▸ η f)
    nd : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f)
      → (δ : (s : Pos o) → 𝕆 (Typ o s))
      → (ε : (s : Pos o) → 𝕆 (Typ o s ▸ δ s))
      → 𝕆 (f ▸ μ o δ)

  -- Not strictly positive with this definition ...
  data Pos where
    ob-pos : Pos ob
    nd-pos-here : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f)
      → (δ : (s : Pos o) → 𝕆 (Typ o s))
      → (ε : (s : Pos o) → 𝕆 (Typ o s ▸ δ s))
      → Pos (nd f o δ ε)
    nd-pos-there : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f)
      → (δ : (s : Pos o) → 𝕆 (Typ o s))
      → (ε : (s : Pos o) → 𝕆 (Typ o s ▸ δ s))
      → (p : Pos o) (q : Pos (ε p))
      → Pos (nd f o δ ε)

  data Face where
    here : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) → Pos o → Face (f ▸ o)
    there : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) → Face f → Face (f ▸ o)


  -- Typ : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f) (s : Pos o) → 𝔽 n
  Typ ob ob-pos = ●
  Typ (lf f) ()
  Typ (nd f o δ ε) (nd-pos-here .f .o .δ .ε) = f ▸ o
  Typ (nd f o δ ε) (nd-pos-there .f .o .δ .ε p q) = Typ (ε p) q

  postulate

    -- η-pos laws
    η-pos-typ : {n : ℕ} (f : 𝔽 n)
      → (p : Pos (η f))
      → Typ (η f) p ↦ f
    {-# REWRITE η-pos-typ #-}

    η-pos-elim-β : {n : ℕ} (f : 𝔽 n)
      → (X : (p : Pos (η f)) → 𝕌)
      → (η-pos* : X (η-pos f))
      → η-pos-elim f X η-pos* (η-pos f) ↦ η-pos*
    {-# REWRITE η-pos-elim-β #-}

    -- μ-pos laws
    μ-pos-fst-β : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
      → (κ : (s : Pos o) → 𝕆 (Typ o s))
      → (s : Pos o) (t : Pos (κ s))
      → μ-pos-fst o κ (μ-pos o κ s t) ↦ s
    {-# REWRITE μ-pos-fst-β #-}

    μ-pos-snd-β : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
      → (κ : (s : Pos o) → 𝕆 (Typ o s))
      → (s : Pos o) (t : Pos (κ s))
      → μ-pos-snd o κ (μ-pos o κ s t) ↦ t
    {-# REWRITE μ-pos-snd-β #-}
    
    μ-pos-η : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
      → (κ : (s : Pos o) → 𝕆 (Typ o s))
      → (s : Pos (μ o κ))
      → μ-pos o κ (μ-pos-fst o κ s) (μ-pos-snd o κ s) ↦ s
    {-# REWRITE μ-pos-η #-}

    μ-pos-typ : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
      → (κ : (s : Pos o) → 𝕆 (Typ o s))
      → (s : Pos (μ o κ))
      → Typ (μ o κ) s ↦ Typ (κ (μ-pos-fst o κ s)) (μ-pos-snd o κ s)
    {-# REWRITE μ-pos-typ #-}

    -- μ laws
    μ-unit-r : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
      → μ o (λ s → η (Typ o s)) ↦ o
    {-# REWRITE μ-unit-r #-}

    μ-unit-l : {n : ℕ} {f : 𝔽 n} (ϕ : (s : Pos (η f)) → 𝕆 f)
      → μ (η f) ϕ ↦ ϕ (η-pos f)
    {-# REWRITE μ-unit-l #-}

    μ-assoc : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
      → (κ : (s : Pos o) → 𝕆 (Typ o s))
      → (θ : (s : Pos (μ o κ)) → 𝕆 (Typ (μ o κ) s))
      → μ (μ o κ) θ ↦ μ o (λ s → μ (κ s) (λ t → θ (μ-pos o κ s t)))
    {-# REWRITE μ-assoc #-}

    -- γ elim rules
    γ-pos-elim-inl-β : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
      → (δ : (s : Pos o) → 𝕆 (Typ o s))
      → (ε : (s : Pos o) → 𝕆 (Typ o s ▸ δ s))
      → (X : Pos (γ f o p δ ε) → 𝕌)
      → (left : (s : Pos p) → X (γ-pos-inl f o p δ ε s))
      → (right : (s : Pos o) (t : Pos (ε s)) → X (γ-pos-inr f o p δ ε s t))
      → (s : Pos p)
      → γ-pos-elim f o p δ ε X left right (γ-pos-inl f o p δ ε s) ↦ left s
    {-# REWRITE γ-pos-elim-inl-β #-}

    γ-pos-elim-inr-β : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
      → (δ : (s : Pos o) → 𝕆 (Typ o s))
      → (ε : (s : Pos o) → 𝕆 (Typ o s ▸ δ s))
      → (X : Pos (γ f o p δ ε) → 𝕌)
      → (left : (s : Pos p) → X (γ-pos-inl f o p δ ε s))
      → (right : (s : Pos o) (t : Pos (ε s)) → X (γ-pos-inr f o p δ ε s t))
      → (s : Pos o) (t : Pos (ε s))
      → γ-pos-elim f o p δ ε X left right (γ-pos-inr f o p δ ε s t) ↦ right s t
    {-# REWRITE γ-pos-elim-inr-β #-}

    -- γ pos laws
    γ-pos-inl-typ : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
      → (δ : (s : Pos o) → 𝕆 (Typ o s))
      → (ε : (s : Pos o) → 𝕆 (Typ o s ▸ δ s))
      → (s : Pos p)
      → Typ (γ f o p δ ε) (γ-pos-inl f o p δ ε s) ↦ Typ p s
    {-# REWRITE γ-pos-inl-typ #-}

    γ-pos-inr-typ : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
      → (δ : (s : Pos o) → 𝕆 (Typ o s))
      → (ε : (s : Pos o) → 𝕆 (Typ o s ▸ δ s))
      → (s : Pos o) (t : Pos (ε s))
      → Typ (γ f o p δ ε) (γ-pos-inr f o p δ ε s t) ↦ Typ (ε s) t
    {-# REWRITE γ-pos-inr-typ #-}

    -- γ laws
    γ-unit-r : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
      → γ f o p (λ s → η (Typ o s)) (λ s → lf (Typ o s)) ↦ p 
    {-# REWRITE γ-unit-r #-}

  -- η : {n : ℕ} (f : 𝔽 n) → 𝕆 f
  η ● = ob
  η (f ▸ o) = nd f o (λ s → η (Typ o s)) (λ s → lf (Typ o s))

  -- η-pos : {n : ℕ} (f : 𝔽 n)
  --   → Pos (η f)
  η-pos ● = ob-pos
  η-pos (f ▸ o) = nd-pos-here f o (λ s → η (Typ o s)) (λ s → lf (Typ o s))
  
  -- η-pos-elim : {n : ℕ} (f : 𝔽 n)
  --   → (X : (p : Pos (η f)) → 𝕌)
  --   → (η-pos* : X (η-pos f))
  --   → (p : Pos (η f)) → X p
  η-pos-elim ● X η-pos* ob-pos = η-pos*
  η-pos-elim (f ▸ o) X η-pos* (nd-pos-here .f .o ._ ._) = η-pos*
  η-pos-elim (f ▸ o) X η-pos* (nd-pos-there .f .o ._ ._ p ())

  -- μ : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
  --   → (κ : (s : Pos o) → 𝕆 (Typ o s))
  --   → 𝕆 f
  μ ob κ = κ ob-pos
  μ (lf f) κ = lf f
  μ (nd f o δ ε) κ =
    let w = κ (nd-pos-here f o δ ε)
        ε' s = μ (ε s) (λ t → κ (nd-pos-there f o δ ε s t))
    in γ f o w δ ε'

  -- γ : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
  --   → (δ : (s : Pos o) → 𝕆 (Typ o s))
  --   → (ε : (s : Pos o) → 𝕆 (Typ o s ▸ δ s))
  --   → 𝕆 (f ▸ μ o δ)
  γ f .(η f) (lf .f) ϕ ψ = ψ (η-pos f)
  γ f .(μ o δ) (nd .f o δ ε) ϕ ψ =
    let ϕ' p q = ϕ (μ-pos o δ p q)
        ψ' p q = ψ (μ-pos o δ p q)
        δ' p = μ (δ p) (ϕ' p)
        ε' p = γ (Typ o p) (δ p) (ε p) (ϕ' p) (ψ' p) 
    in nd f o δ' ε'

  -- μ-pos : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
  --   → (κ : (s : Pos o) → 𝕆 (Typ o s))
  --   → (s : Pos o) (t : Pos (κ s))
  --   → Pos (μ o κ)
  μ-pos ob κ ob-pos q = q
  μ-pos (lf f) κ () q
  μ-pos (nd f o δ ε) κ (nd-pos-here .f .o .δ .ε) r =
    let w = κ (nd-pos-here f o δ ε)
        ε' s = μ (ε s) (λ t → κ (nd-pos-there f o δ ε s t))
    in γ-pos-inl f o w δ ε' r
  μ-pos (nd f o δ ε) κ (nd-pos-there .f .o .δ .ε p q) r = 
    let w = κ (nd-pos-here f o δ ε)
        κ' s t = κ (nd-pos-there f o δ ε s t)
        ε' s = μ (ε s) (κ' s)
    in γ-pos-inr f o w δ ε' p (μ-pos (ε p) (κ' p) q r) 

  -- μ-pos-fst : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
  --   → (κ : (s : Pos o) → 𝕆 (Typ o s))
  --   → Pos (μ o κ) → Pos o
  μ-pos-fst ob κ _ = ob-pos
  μ-pos-fst (lf f) κ ()
  μ-pos-fst (nd f o δ ε) κ =
    let w = κ (nd-pos-here f o δ ε)
        κ' s t = κ (nd-pos-there f o δ ε s t)
        ε' s = μ (ε s) (κ' s)
    in γ-pos-elim f o w δ ε' _ (λ _ → nd-pos-here f o δ ε) 
         (λ s t → nd-pos-there f o δ ε s (μ-pos-fst (ε s) (κ' s) t))
    
  -- μ-pos-snd : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
  --   → (κ : (s : Pos o) → 𝕆 (Typ o s))
  --   → (s : Pos (μ o κ)) → Pos (κ (μ-pos-fst o κ s))
  μ-pos-snd ob κ p = p
  μ-pos-snd (lf f) κ ()
  μ-pos-snd (nd f o δ ε) κ = 
    let w = κ (nd-pos-here f o δ ε)
        κ' s t = κ (nd-pos-there f o δ ε s t)
        ε' s = μ (ε s) (κ' s)
    in γ-pos-elim f o w δ ε' _ (λ s → s)
         (λ s t → μ-pos-snd (ε s) (κ' s) t)

  -- γ-pos-inl : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
  --   → (δ : (s : Pos o) → 𝕆 (Typ o s))
  --   → (ε : (s : Pos o) → 𝕆 (Typ o s ▸ δ s))
  --   → Pos p → Pos (γ f o p δ ε)
  γ-pos-inl f .(η f) (lf .f) ϕ ψ ()
  γ-pos-inl f .(μ o δ) (nd .f o δ ε) ϕ ψ (nd-pos-here .f .o .δ .ε) = 
    let ϕ' p q = ϕ (μ-pos o δ p q)
        ψ' p q = ψ (μ-pos o δ p q)
        δ' p = μ (δ p) (ϕ' p)
        ε' p = γ (Typ o p) (δ p) (ε p) (ϕ' p) (ψ' p)
    in nd-pos-here f o δ' ε'
  γ-pos-inl f .(μ o δ) (nd .f o δ ε) ϕ ψ (nd-pos-there .f .o .δ .ε u v) = 
    let ϕ' p q = ϕ (μ-pos o δ p q)
        ψ' p q = ψ (μ-pos o δ p q)
        δ' p = μ (δ p) (ϕ' p)
        ε' p = γ (Typ o p) (δ p) (ε p) (ϕ' p) (ψ' p)
    in nd-pos-there f o δ' ε' u (γ-pos-inl (Typ o u) (δ u) (ε u) (ϕ' u) (ψ' u) v)

  -- γ-pos-inr : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
  --   → (δ : (s : Pos o) → 𝕆 (Typ o s))
  --   → (ε : (s : Pos o) → 𝕆 (Typ o s ▸ δ s))
  --   → (s : Pos o) (t : Pos (ε s))
  --   → Pos (γ f o p δ ε)
  γ-pos-inr f .(η f) (lf .f) ϕ ψ =
    η-pos-elim f (λ p → Pos (ψ p) → Pos (ψ (η-pos f))) (λ p → p) 
  γ-pos-inr f .(μ o δ) (nd .f o δ ε) ϕ ψ u v = 
    let ϕ' p q = ϕ (μ-pos o δ p q)
        ψ' p q = ψ (μ-pos o δ p q)
        δ' p = μ (δ p) (ϕ' p)
        ε' p = γ (Typ o p) (δ p) (ε p) (ϕ' p) (ψ' p)
        u₀ = μ-pos-fst o δ u
        u₁ = μ-pos-snd o δ u
    in nd-pos-there f o δ' ε' u₀ (γ-pos-inr (Typ o u₀) (δ u₀) (ε u₀) (ϕ' u₀) (ψ' u₀) u₁ v)

  -- γ-pos-elim : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
  --   → (δ : (s : Pos o) → 𝕆 (Typ o s))
  --   → (ε : (s : Pos o) → 𝕆 (Typ o s ▸ δ s))
  --   → (X : Pos (γ f o p δ ε) → 𝕌)
  --   → (left : (s : Pos p) → X (γ-pos-inl f o p δ ε s))
  --   → (right : (s : Pos o) (t : Pos (ε s)) → X (γ-pos-inr f o p δ ε s t))
  --   → (s : Pos (γ f o p δ ε)) → X s
  γ-pos-elim f .(η f) (lf .f) ϕ ψ X inl* inr* q = inr* (η-pos f) q
  γ-pos-elim f .(μ o δ) (nd .f o δ ε) ϕ ψ X inl* inr* (nd-pos-here .f .o ._ ._) =
    inl* (nd-pos-here f o δ ε)
  γ-pos-elim f .(μ o δ) (nd .f o δ ε) ϕ ψ X inl* inr* (nd-pos-there .f .o ._ ._ u v) =
    let ϕ' p q = ϕ (μ-pos o δ p q)
        ψ' p q = ψ (μ-pos o δ p q)
        δ' p = μ (δ p) (ϕ' p)
        ε' p = γ (Typ o p) (δ p) (ε p) (ϕ' p) (ψ' p)
    in γ-pos-elim (Typ o u) (δ u) (ε u) (ϕ' u) (ψ' u)
         (λ t → X (nd-pos-there f o δ' ε' u t))
         (λ t → inl* (nd-pos-there f o δ ε u t))
         (λ s t → inr* (μ-pos o δ u s) t) v

