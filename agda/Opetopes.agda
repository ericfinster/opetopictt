{-# OPTIONS --without-K --rewriting #-}

open import HoTT

--
--  There is a bug here with respect to the treatment of
--  objects, as there should be a unique position for an
--  object and the various functions must be updated to
--  reflect this.  It is treated correctly in the typed
--  version .... (hence this file should be considered
--  out of date ...)
--

module Opetopes where

  data 𝔽 : ℕ → Type₀
  data 𝕆 : {n : ℕ} (f : 𝔽 n) → Type₀

  infixl 40 _▸_

  data 𝔽 where
    ● : 𝔽 O
    _▸_ : {n : ℕ} (f : 𝔽 n) → 𝕆 f → 𝔽 (S n)

  postulate
  
    Src : {n : ℕ} {f : 𝔽 n} → 𝕆 f → Type₀

  Typ : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f) (s : Src o) → 𝔽 n

  η : {n : ℕ} (f : 𝔽 n) → 𝕆 f

  μ : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
    → (κ : (s : Src o) → 𝕆 (Typ o s))
    → 𝕆 f

  μ-src : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
    → (κ : (s : Src o) → 𝕆 (Typ o s))
    → (s : Src o) (t : Src (κ s))
    → Src (μ o κ)

  μ-src-fst : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
    → (κ : (s : Src o) → 𝕆 (Typ o s))
    → Src (μ o κ) → Src o

  μ-src-snd : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
    → (κ : (s : Src o) → 𝕆 (Typ o s))
    → (s : Src (μ o κ)) → Src (κ (μ-src-fst o κ s))

  γ : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
    → (δ : (s : Src o) → 𝕆 (Typ o s))
    → (ε : (s : Src o) → 𝕆 (Typ o s ▸ δ s))
    → 𝕆 (f ▸ μ o δ)

  γ-src-inl : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
    → (δ : (s : Src o) → 𝕆 (Typ o s))
    → (ε : (s : Src o) → 𝕆 (Typ o s ▸ δ s))
    → Src p → Src (γ f o p δ ε)

  γ-src-inr : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
    → (δ : (s : Src o) → 𝕆 (Typ o s))
    → (ε : (s : Src o) → 𝕆 (Typ o s ▸ δ s))
    → (s : Src o) (t : Src (ε s))
    → Src (γ f o p δ ε)

  γ-src-elim : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
    → (δ : (s : Src o) → 𝕆 (Typ o s))
    → (ε : (s : Src o) → 𝕆 (Typ o s ▸ δ s))
    → (X : Src (γ f o p δ ε) → Type₀)
    → (left : (s : Src p) → X (γ-src-inl f o p δ ε s))
    → (right : (s : Src o) (t : Src (ε s)) → X (γ-src-inr f o p δ ε s t))
    → (s : Src (γ f o p δ ε)) → X s

  data 𝕆 where
    ob : 𝕆 ●
    lf : {n : ℕ} (f : 𝔽 n) → 𝕆 (f ▸ η f)
    nd : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f)
      → (δ : (s : Src o) → 𝕆 (Typ o s))
      → (ε : (s : Src o) → 𝕆 (Typ o s ▸ δ s))
      → 𝕆 (f ▸ μ o δ)

  postulate
  
    ob-src-elim : (X : Src ob → Type₀)
      → (s : Src ob) → X s

    lf-src-elim : {n : ℕ} (f : 𝔽 n) (X : Src (lf f) → Type₀)
      → (s : Src (lf f)) → X s
      
    nd-src-here : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f)
        → (δ : (s : Src o) → 𝕆 (Typ o s))
        → (ε : (s : Src o) → 𝕆 (Typ o s ▸ δ s))
        → Src (nd f o δ ε)
        
    nd-src-there : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f)
        → (δ : (s : Src o) → 𝕆 (Typ o s))
        → (ε : (s : Src o) → 𝕆 (Typ o s ▸ δ s))
        → (s : Src o) (t : Src (ε s))
        → Src (nd f o δ ε)
      
    nd-src-elim : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f)
        → (δ : (s : Src o) → 𝕆 (Typ o s))
        → (ε : (s : Src o) → 𝕆 (Typ o s ▸ δ s))
        → (X : Src (nd f o δ ε) → Type₀)
        → (hr : X (nd-src-here f o δ ε))
        → (thr : (s : Src o) (t : Src (ε s))
                 → X (nd-src-there f o δ ε s t))
        → (s : Src (nd f o δ ε)) → X s

    nd-src-elim-here-β : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f)
        → (δ : (s : Src o) → 𝕆 (Typ o s))
        → (ε : (s : Src o) → 𝕆 (Typ o s ▸ δ s))
        → (X : Src (nd f o δ ε) → Type₀)
        → (hr : X (nd-src-here f o δ ε))
        → (thr : (s : Src o) (t : Src (ε s))
                 → X (nd-src-there f o δ ε s t))
        → nd-src-elim f o δ ε X hr thr (nd-src-here f o δ ε) ↦ hr
    {-# REWRITE nd-src-elim-here-β #-}

    nd-src-elim-there-β : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f)
        → (δ : (s : Src o) → 𝕆 (Typ o s))
        → (ε : (s : Src o) → 𝕆 (Typ o s ▸ δ s))
        → (X : Src (nd f o δ ε) → Type₀)
        → (hr : X (nd-src-here f o δ ε))
        → (thr : (s : Src o) (t : Src (ε s))
                 → X (nd-src-there f o δ ε s t))
        → (s : Src o) (t : Src (ε s))
        → nd-src-elim f o δ ε X hr thr (nd-src-there f o δ ε s t) ↦ thr s t
    {-# REWRITE nd-src-elim-there-β #-}

  -- Typ : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f) (s : Src o) → 𝔽 n
  Typ ob = ob-src-elim (λ _ → 𝔽 0)
  Typ (lf {n} f) = lf-src-elim f (λ _ → 𝔽 (S n)) 
  Typ (nd {n} f o δ ε) = nd-src-elim f o δ ε
    (λ _ → 𝔽 (S n)) (f ▸ o) (λ s t → Typ (ε s) t)

  postulate
  
    -- μ-src laws
    μ-src-fst-β : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
      → (κ : (s : Src o) → 𝕆 (Typ o s))
      → (s : Src o) (t : Src (κ s))
      → μ-src-fst o κ (μ-src o κ s t) ↦ s
    {-# REWRITE μ-src-fst-β #-}

    μ-src-snd-β : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
      → (κ : (s : Src o) → 𝕆 (Typ o s))
      → (s : Src o) (t : Src (κ s))
      → μ-src-snd o κ (μ-src o κ s t) ↦ t
    {-# REWRITE μ-src-snd-β #-}
    
    μ-src-η : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
      → (κ : (s : Src o) → 𝕆 (Typ o s))
      → (s : Src (μ o κ))
      → μ-src o κ (μ-src-fst o κ s) (μ-src-snd o κ s) ↦ s
    {-# REWRITE μ-src-η #-}

    μ-src-typ : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
      → (κ : (s : Src o) → 𝕆 (Typ o s))
      → (s : Src (μ o κ))
      → Typ (μ o κ) s ↦ Typ (κ (μ-src-fst o κ s)) (μ-src-snd o κ s)
    {-# REWRITE μ-src-typ #-}

    -- μ laws
    μ-unit-r : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f) → μ o (λ s → η (Typ o s)) ↦ o
    {-# REWRITE μ-unit-r #-}

    μ-assoc : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
      → (κ : (s : Src o) → 𝕆 (Typ o s))
      → (θ : (s : Src (μ o κ)) → 𝕆 (Typ (μ o κ) s))
      → μ (μ o κ) θ ↦ μ o (λ s → μ (κ s) (λ t → θ (μ-src o κ s t)))
    {-# REWRITE μ-assoc #-}

    -- γ elim rules
    γ-src-elim-inl-β : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
      → (δ : (s : Src o) → 𝕆 (Typ o s))
      → (ε : (s : Src o) → 𝕆 (Typ o s ▸ δ s))
      → (X : Src (γ f o p δ ε) → Type₀)
      → (left : (s : Src p) → X (γ-src-inl f o p δ ε s))
      → (right : (s : Src o) (t : Src (ε s)) → X (γ-src-inr f o p δ ε s t))
      → (s : Src p)
      → γ-src-elim f o p δ ε X left right (γ-src-inl f o p δ ε s) ↦ left s
    {-# REWRITE γ-src-elim-inl-β #-}

    γ-src-elim-inr-β : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
      → (δ : (s : Src o) → 𝕆 (Typ o s))
      → (ε : (s : Src o) → 𝕆 (Typ o s ▸ δ s))
      → (X : Src (γ f o p δ ε) → Type₀)
      → (left : (s : Src p) → X (γ-src-inl f o p δ ε s))
      → (right : (s : Src o) (t : Src (ε s)) → X (γ-src-inr f o p δ ε s t))
      → (s : Src o) (t : Src (ε s))
      → γ-src-elim f o p δ ε X left right (γ-src-inr f o p δ ε s t) ↦ right s t
    {-# REWRITE γ-src-elim-inr-β #-}

    -- γ src laws
    γ-src-inl-typ : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
      → (δ : (s : Src o) → 𝕆 (Typ o s))
      → (ε : (s : Src o) → 𝕆 (Typ o s ▸ δ s))
      → (s : Src p)
      → Typ (γ f o p δ ε) (γ-src-inl f o p δ ε s) ↦ Typ p s
    {-# REWRITE γ-src-inl-typ #-}

    γ-src-inr-typ : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
      → (δ : (s : Src o) → 𝕆 (Typ o s))
      → (ε : (s : Src o) → 𝕆 (Typ o s ▸ δ s))
      → (s : Src o) (t : Src (ε s))
      → Typ (γ f o p δ ε) (γ-src-inr f o p δ ε s t) ↦ Typ (ε s) t
    {-# REWRITE γ-src-inr-typ #-}

    -- γ laws
    γ-unit-r : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
      → γ f o p (λ s → η (Typ o s)) (λ s → lf (Typ o s)) ↦ p 
    {-# REWRITE γ-unit-r #-}

  -- η : {n : ℕ} (f : 𝔽 n) → 𝕆 f
  η ● = ob
  η (f ▸ o) = nd f o (λ s → η (Typ o s)) (λ s → lf (Typ o s))

  -- μ : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
  --   → (κ : (s : Src o) → 𝕆 (Typ o s))
  --   → 𝕆 f
  μ ob κ = ob
  μ (lf f) κ = lf f
  μ (nd f o δ ε) κ =
    let w = κ (nd-src-here f o δ ε)
        ε' s = μ (ε s) (λ t → κ (nd-src-there f o δ ε s t))
    in γ f o w δ ε'

  -- γ : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
  --   → (δ : (s : Src o) → 𝕆 (Typ o s))
  --   → (ε : (s : Src o) → 𝕆 (Typ o s ▸ δ s))
  --   → 𝕆 (f ▸ μ o δ)
  γ ● ob p δ' ε' = p
  γ (f ▸ o) .(η (f ▸ o)) (lf .(f ▸ o)) δ' ε' =
    ε' (nd-src-here f o (λ s → η (Typ o s)) (λ s → lf (Typ o s)))
  γ (f ▸ o) .(μ q δ) (nd .(f ▸ o) q δ ε) δ' ε' =
    let δ'' s = μ (δ s) (λ t → δ' (μ-src q δ s t))
        ε'' s = γ (Typ q s) (δ s) (ε s) (λ t → δ' (μ-src q δ s t)) (λ t → ε' (μ-src q δ s t))
    in nd (f ▸ o) q δ'' ε''

  -- μ-src : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
  --   → (κ : (s : Src o) → 𝕆 (Typ o s))
  --   → (s : Src o) (t : Src (κ s))
  --   → Src (μ o κ)
  μ-src ob κ = ob-src-elim (λ s → Src (κ s) → Src ob)
  μ-src (lf f) κ = lf-src-elim f (λ s → Src (κ s) → Src (lf f))
  μ-src (nd f o δ ε) κ = nd-src-elim f o δ ε (λ s₀ → Src (κ s₀) → Src (μ (nd f o δ ε) κ))
    (γ-src-inl f o (κ (nd-src-here f o δ ε)) δ (λ s → μ (ε s) (λ t → κ (nd-src-there f o δ ε s t))))
    (λ s t u → γ-src-inr f o (κ (nd-src-here f o δ ε)) δ
                 (λ s₁ → μ (ε s₁) (λ t₁ → κ (nd-src-there f o δ ε s₁ t₁))) s
                           (μ-src (ε s) (λ t → κ (nd-src-there f o δ ε s t)) t u))


  -- μ-src-fst : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
  --   → (κ : (s : Src o) → 𝕆 (Typ o s))
  --   → Src (μ o κ) → Src o
  μ-src-fst ob κ = ob-src-elim (λ _ → Src ob)
  μ-src-fst (lf f) κ = lf-src-elim f (λ _ → Src (lf f))
  μ-src-fst (nd f o δ ε) κ = 
    let w = κ (nd-src-here f o δ ε)
        ε' s = μ (ε s) (λ t → κ (nd-src-there f o δ ε s t))
    in γ-src-elim f o w δ ε' _
         (λ _ → nd-src-here f o δ ε)
         (λ s t → nd-src-there f o δ ε s (μ-src-fst (ε s) (λ t₁ → κ (nd-src-there f o δ ε s t₁)) t))
    
  -- μ-src-snd : {n : ℕ} {f : 𝔽 n} (o : 𝕆 f)
  --   → (κ : (s : Src o) → 𝕆 (Typ o s))
  --   → (s : Src (μ o κ)) → Src (κ (μ-src-fst o κ s))
  μ-src-snd ob κ = ob-src-elim _
  μ-src-snd (lf f) κ = lf-src-elim f _
  μ-src-snd (nd f o δ ε) κ = 
    let w = κ (nd-src-here f o δ ε)
        ε' s = μ (ε s) (λ t → κ (nd-src-there f o δ ε s t))
    in γ-src-elim f o w δ ε' _
         (λ s → s)
         (λ s t → μ-src-snd (ε s) (λ t₁ → κ (nd-src-there f o δ ε s t₁)) t)

  -- γ-src-inl : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
  --   → (δ : (s : Src o) → 𝕆 (Typ o s))
  --   → (ε : (s : Src o) → 𝕆 (Typ o s ▸ δ s))
  --   → Src p → Src (γ f o p δ ε)
  γ-src-inl ● ob p δ ε s = s
  γ-src-inl (f ▸ o) .(η (f ▸ o)) (lf .(f ▸ o)) δ ε =
    lf-src-elim (f ▸ o) _ 
  γ-src-inl (f ▸ o) .(μ q δ) (nd .(f ▸ o) q δ ε) δ' ε' = 
    nd-src-elim (f ▸ o) q δ ε _
      (nd-src-here (f ▸ o) q _ _)
      (λ s t → nd-src-there (f ▸ o) q _ _ s
                 (γ-src-inl (Typ q s) (δ s) (ε s)
                   (λ t' → δ' (μ-src q δ s t'))
                   (λ t' → ε' (μ-src q δ s t')) t))

  -- γ-src-inr : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
  --   → (δ : (s : Src o) → 𝕆 (Typ o s))
  --   → (ε : (s : Src o) → 𝕆 (Typ o s ▸ δ s))
  --   → (s : Src o) (t : Src (ε s))
  --   → Src (γ f o p δ ε)
  γ-src-inr ● ob p δ ε = ob-src-elim (λ s → Src (ε s) → Src p)
  γ-src-inr (f ▸ o) .(η (f ▸ o)) (lf .(f ▸ o)) δ ε =
    nd-src-elim f o (λ s → η (Typ o s)) (λ s → lf (Typ o s)) _
      (λ t → t) (λ s → lf-src-elim (Typ o s) _)
  γ-src-inr (f ▸ o) .(μ q δ) (nd .(f ▸ o) q δ ε) δ' ε' s t = 
    let s₀ = μ-src-fst q δ s
        s₁ = μ-src-snd q δ s
        δ'' t₀ = δ' (μ-src q δ s₀ t₀)
        ε'' t₀ = ε' (μ-src q δ s₀ t₀)
    in nd-src-there (f ▸ o) q _ _ s₀ 
         (γ-src-inr (Typ q s₀) (δ s₀) (ε s₀) δ'' ε'' s₁ t)

  -- γ-src-elim : {n : ℕ} (f : 𝔽 n) (o : 𝕆 f) (p : 𝕆 (f ▸ o))
  --   → (δ : (s : Src o) → 𝕆 (Typ o s))
  --   → (ε : (s : Src o) → 𝕆 (Typ o s ▸ δ s))
  --   → (X : Src (γ f o p δ ε) → Type₀)
  --   → (left : (s : Src p) → X (γ-src-inl f o p δ ε s))
  --   → (right : (s : Src o) (t : Src (ε s)) → X (γ-src-inr f o p δ ε s t))
  --   → (s : Src (γ f o p δ ε)) → X s
  γ-src-elim ● ob p δ ε X left right s = left s
  γ-src-elim (f ▸ o) .(η (f ▸ o)) (lf .(f ▸ o)) δ ε X left right s =
    right (nd-src-here f o (λ s₁ → η (Typ o s₁)) (λ s₁ → lf (Typ o s₁))) s
  γ-src-elim (f ▸ o) .(μ q δ) (nd .(f ▸ o) q δ ε) δ' ε' X left right = 
    let δ'' s = μ (δ s) (λ t → δ' (μ-src q δ s t))
        ε'' s = γ (Typ q s) (δ s) (ε s) (λ t → δ' (μ-src q δ s t)) (λ t → ε' (μ-src q δ s t))
    in nd-src-elim (f ▸ o) q δ'' ε'' X
         (left (nd-src-here (f ▸ o) q δ ε))
         (λ s → γ-src-elim (Typ q s) (δ s) (ε s) (λ t₁ → δ' (μ-src q δ s t₁)) (λ t₁ → ε' (μ-src q δ s t₁))
                   (λ t → X (nd-src-there (f ▸ o) q
                              (λ s₁ → μ (δ s₁) (λ t₁ → δ' (μ-src q δ s₁ t₁)))
                              (λ s₁ → γ (Typ q s₁) (δ s₁) (ε s₁) (λ t₁ → δ' (μ-src q δ s₁ t₁))
                              (λ t₁ → ε' (μ-src q δ s₁ t₁))) s t))
                   (λ s' → left (nd-src-there (f ▸ o) q δ ε s s'))
                   (λ s' t → right (μ-src q δ s s') t))

