{-# OPTIONS --without-K --rewriting #-}

open import Base

module Opetopes where

  data 𝕆 : ℕ → Set
  data 𝕋 : {n : ℕ} → 𝕆 n → Set
  
  Posₒ : {n : ℕ} {o : 𝕆 n} → 𝕋 o → Set
  Typₒ : {n : ℕ} {o : 𝕆 n}
    → (t : 𝕋 o) (p : Posₒ t)
    → 𝕆 n 

  infixl 40 _▸_
  
  data 𝕆 where
    ● : 𝕆 O
    _▸_ : {n : ℕ} (o : 𝕆 n) (t : 𝕋 o) → 𝕆 (S n)

  ηₒ : {n : ℕ} (o : 𝕆 n) → 𝕋 o

  ηₒ-pos : {n : ℕ} (o : 𝕆 n)
    → Posₒ (ηₒ o)

  ηₒ-pos-elim : {n : ℕ} (o : 𝕆 n)
    → (X : (p : Posₒ (ηₒ o)) → Set)
    → (η-pos* : X (ηₒ-pos o))
    → (p : Posₒ (ηₒ o)) → X p

  μₒ : {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
    → (κ : (p : Posₒ t) → 𝕋 (Typₒ t p))
    → 𝕋 o

  μₒ-pos : {n : ℕ} {o : 𝕆 n} (o : 𝕋 o)
    → (κ : (p : Posₒ o) → 𝕋 (Typₒ o p))
    → (p : Posₒ o) (t : Posₒ (κ p))
    → Posₒ (μₒ o κ)

  μₒ-pos-fst : {n : ℕ} {o : 𝕆 n} (o : 𝕋 o)
    → (κ : (p : Posₒ o) → 𝕋 (Typₒ o p))
    → Posₒ (μₒ o κ) → Posₒ o

  μₒ-pos-snd : {n : ℕ} {o : 𝕆 n} (o : 𝕋 o)
    → (κ : (p : Posₒ o) → 𝕋 (Typₒ o p))
    → (p : Posₒ (μₒ o κ)) → Posₒ (κ (μₒ-pos-fst o κ p))

  γₒ : {n : ℕ} (o : 𝕆 n) (s : 𝕋 o) (t : 𝕋 (o ▸ s))
    → (δ : (p : Posₒ s) → 𝕋 (Typₒ s p))
    → (ε : (p : Posₒ s) → 𝕋 (Typₒ s p ▸ δ p))
    → 𝕋 (o ▸ μₒ s δ)

  γₒ-pos-inl : {n : ℕ} (o : 𝕆 n) (s : 𝕋 o) (t : 𝕋 (o ▸ s))
    → (δ : (p : Posₒ s) → 𝕋 (Typₒ s p))
    → (ε : (p : Posₒ s) → 𝕋 (Typₒ s p ▸ δ p))
    → Posₒ t → Posₒ (γₒ o s t δ ε)

  γₒ-pos-inr : {n : ℕ} (o : 𝕆 n) (s : 𝕋 o) (t : 𝕋 (o ▸ s))
    → (δ : (p : Posₒ s) → 𝕋 (Typₒ s p))
    → (ε : (p : Posₒ s) → 𝕋 (Typₒ s p ▸ δ p))
    → (p : Posₒ s) (q : Posₒ (ε p))
    → Posₒ (γₒ o s t δ ε)

  γₒ-pos-elim : {n : ℕ} (o : 𝕆 n) (s : 𝕋 o) (t : 𝕋 (o ▸ s))
    → (δ : (p : Posₒ s) → 𝕋 (Typₒ s p))
    → (ε : (p : Posₒ s) → 𝕋 (Typₒ s p ▸ δ p))
    → (X : Posₒ (γₒ o s t δ ε) → Set)
    → (inl* : (p : Posₒ t) → X (γₒ-pos-inl o s t δ ε p))
    → (inr* : (p : Posₒ s) (q : Posₒ (ε p)) → X (γₒ-pos-inr o s t δ ε p q))
    → (p : Posₒ (γₒ o s t δ ε)) → X p

  data 𝕋 where
    arr : 𝕋 ●
    lf : {n : ℕ} (o : 𝕆 n) → 𝕋 (o ▸ ηₒ o)
    nd : {n : ℕ} (o : 𝕆 n) (t : 𝕋 o)
      → (δ : (p : Posₒ t) → 𝕋 (Typₒ t p))
      → (ε : (p : Posₒ t) → 𝕋 (Typₒ t p ▸ δ p))
      → 𝕋 (o ▸ μₒ t δ)

  Posₒ arr = ⊤
  Posₒ (lf o) = ⊥
  Posₒ (nd o t δ ε) = ⊤ ⊔ Σ (Posₒ t) (λ p → Posₒ (ε p))
  
  Typₒ arr unit = ●
  Typₒ (nd o t δ ε) (inl unit) = o ▸ t
  Typₒ (nd o t δ ε) (inr (p , q)) = Typₒ (ε p) q

  postulate

    -- ηₒ-pos laws
    ηₒ-pos-typ : {n : ℕ} (o : 𝕆 n)
      → (p : Posₒ (ηₒ o))
      → Typₒ (ηₒ o) p ↦ o
    {-# REWRITE ηₒ-pos-typ #-}

    ηₒ-pos-elim-β : {n : ℕ} (o : 𝕆 n)
      → (X : (p : Posₒ (ηₒ o)) → Set)
      → (ηₒ-pos* : X (ηₒ-pos o))
      → ηₒ-pos-elim o X ηₒ-pos* (ηₒ-pos o) ↦ ηₒ-pos*
    {-# REWRITE ηₒ-pos-elim-β #-}

    -- μₒ-pos laws
    μₒ-pos-typ : {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
      → (κ : (p : Posₒ t) → 𝕋 (Typₒ t p))
      → (p : Posₒ (μₒ t κ))
      → Typₒ (μₒ t κ) p ↦ Typₒ (κ (μₒ-pos-fst t κ p)) (μₒ-pos-snd t κ p)
    {-# REWRITE μₒ-pos-typ #-}
  
    μₒ-pos-fst-β : {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
      → (κ : (p : Posₒ t) → 𝕋 (Typₒ t p))
      → (p : Posₒ t) (q : Posₒ (κ p))
      → μₒ-pos-fst t κ (μₒ-pos t κ p q) ↦ p
    {-# REWRITE μₒ-pos-fst-β #-}

    μₒ-pos-snd-β : {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
      → (κ : (p : Posₒ t) → 𝕋 (Typₒ t p))
      → (p : Posₒ t) (q : Posₒ (κ p))
      → μₒ-pos-snd t κ (μₒ-pos t κ p q) ↦ q
    {-# REWRITE μₒ-pos-snd-β #-}
    
    μₒ-pos-η : {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
      → (κ : (p : Posₒ t) → 𝕋 (Typₒ t p))
      → (p : Posₒ (μₒ t κ))
      → μₒ-pos t κ (μₒ-pos-fst t κ p) (μₒ-pos-snd t κ p) ↦ p
    {-# REWRITE μₒ-pos-η #-}

    -- μₒ laws
    μₒ-unit-r : {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
      → μₒ t (λ p → ηₒ (Typₒ t p)) ↦ t
    {-# REWRITE μₒ-unit-r #-}

    μₒ-unit-l : {n : ℕ} {o : 𝕆 n} (ϕ : (p : Posₒ (ηₒ o)) → 𝕋 o)
      → μₒ (ηₒ o) ϕ ↦ ϕ (ηₒ-pos o)
    {-# REWRITE μₒ-unit-l #-}

    μₒ-assoc : {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
      → (κ : (p : Posₒ t) → 𝕋 (Typₒ t p))
      → (θ : (p : Posₒ (μₒ t κ)) → 𝕋 (Typₒ (μₒ t κ) p))
      → μₒ (μₒ t κ) θ ↦ μₒ t (λ p → μₒ (κ p) (λ q → θ (μₒ-pos t κ p q)))
    {-# REWRITE μₒ-assoc #-}

    -- γₒ elim rules
    γₒ-pos-elim-inl-β : {n : ℕ} (o : 𝕆 n) (s : 𝕋 o) (t : 𝕋 (o ▸ s))
      → (δ : (p : Posₒ s) → 𝕋 (Typₒ s p))
      → (ε : (p : Posₒ s) → 𝕋 (Typₒ s p ▸ δ p))
      → (X : Posₒ (γₒ o s t δ ε) → Set)
      → (inl* : (p : Posₒ t) → X (γₒ-pos-inl o s t δ ε p))
      → (inr* : (p : Posₒ s) (q : Posₒ (ε p)) → X (γₒ-pos-inr o s t δ ε p q))
      → (p : Posₒ t)
      → γₒ-pos-elim o s t δ ε X inl* inr* (γₒ-pos-inl o s t δ ε p) ↦ inl* p
    {-# REWRITE γₒ-pos-elim-inl-β #-}

    γₒ-pos-elim-inr-β : {n : ℕ} (o : 𝕆 n) (s : 𝕋 o) (t : 𝕋 (o ▸ s))
      → (δ : (p : Posₒ s) → 𝕋 (Typₒ s p))
      → (ε : (p : Posₒ s) → 𝕋 (Typₒ s p ▸ δ p))
      → (X : Posₒ (γₒ o s t δ ε) → Set)
      → (inl* : (p : Posₒ t) → X (γₒ-pos-inl o s t δ ε p))
      → (inr* : (p : Posₒ s) (q : Posₒ (ε p)) → X (γₒ-pos-inr o s t δ ε p q))
      → (p : Posₒ s) (q : Posₒ (ε p))
      → γₒ-pos-elim o s t δ ε X inl* inr* (γₒ-pos-inr o s t δ ε p q) ↦ inr* p q
    {-# REWRITE γₒ-pos-elim-inr-β #-}

  --   -- γₒ pos laws
  --   γₒ-pos-inl-typ : {n : ℕ} (o : 𝕆 n) (t : 𝕋 o) (t : 𝕋 (f ▸ o))
  --     → (δ : (p : Posₒ o) → 𝕋 (Typₒ o s))
  --     → (ε : (p : Posₒ o) → 𝕋 (Typₒ o s ▸ δ s))
  --     → (p : Posₒ p)
  --     → Typₒ (γₒ f o p δ ε) (γₒ-pos-inl f o p δ ε s) ↦ Typₒ p s
  --   {-# REWRITE γₒ-pos-inl-typ #-}

  --   γₒ-pos-inr-typ : {n : ℕ} (o : 𝕆 n) (t : 𝕋 o) (t : 𝕋 (f ▸ o))
  --     → (δ : (p : Posₒ o) → 𝕋 (Typₒ o s))
  --     → (ε : (p : Posₒ o) → 𝕋 (Typₒ o s ▸ δ s))
  --     → (p : Posₒ o) (t : Posₒ (ε s))
  --     → Typₒ (γₒ f o p δ ε) (γₒ-pos-inr f o p δ ε s t) ↦ Typₒ (ε s) t
  --   {-# REWRITE γₒ-pos-inr-typ #-}

  --   -- γₒ laws
  --   γₒ-unit-r : {n : ℕ} (o : 𝕆 n) (t : 𝕋 o) (t : 𝕋 (f ▸ o))
  --     → γₒ f o p (λ s → η (Typₒ o s)) (λ s → lf (Typₒ o s)) ↦ p 
  --   {-# REWRITE γₒ-unit-r #-}

  ηₒ ● = arr
  ηₒ (o ▸ t) =
    let η-dec p = ηₒ (Typₒ t p)
        lf-dec p = lf (Typₒ t p)
    in nd o t η-dec lf-dec
  
  ηₒ-pos ● = unit
  ηₒ-pos (o ▸ t) = inl unit
  
  ηₒ-pos-elim ● X η-pos* unit = η-pos*
  ηₒ-pos-elim (o ▸ t) X η-pos* (inl unit) = η-pos*

  μₒ arr κ = κ unit
  μₒ (lf o) κ = lf o
  μₒ (nd o t δ ε) κ = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ϕ p = μₒ (ε p) (κ↑ p)
    in γₒ o t w δ ϕ

  μₒ-pos arr κ unit q = q
  μₒ-pos (nd o t δ ε) κ (inl unit) r = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ϕ p = μₒ (ε p) (κ↑ p)
    in γₒ-pos-inl o t w δ ϕ r 
  μₒ-pos (nd o t δ ε) κ (inr (p , q)) r = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ϕ p = μₒ (ε p) (κ↑ p)
    in γₒ-pos-inr o t w δ ϕ p (μₒ-pos (ε p) (κ↑ p) q r)

  μₒ-pos-fst arr κ p = unit
  μₒ-pos-fst (nd o t δ ε) κ p =
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ϕ p = μₒ (ε p) (κ↑ p)
        X _ = ⊤ ⊔ Σ (Posₒ t) (λ q → Posₒ (ε q))
        inl* p = inl unit
        inr* p q = inr (p , (μₒ-pos-fst (ε p) (κ↑ p) q))
    in γₒ-pos-elim o t w δ ϕ X inl* inr* p
    
  μₒ-pos-snd arr κ p = p
  μₒ-pos-snd (nd o t δ ε) κ p = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ϕ p = μₒ (ε p) (κ↑ p)
        X p = Posₒ (κ (μₒ-pos-fst (nd o t δ ε) κ p))
        inl* p = p
        inr* p q = μₒ-pos-snd (ε p) (κ↑ p) q
    in γₒ-pos-elim o t w δ ϕ X inl* inr* p

  γₒ o .(ηₒ o) (lf .o) ϕ ψ = ψ (ηₒ-pos o)
  γₒ o .(μₒ t δ) (nd .o t δ ε) ϕ ψ =
    let ϕ↑ p q = ϕ (μₒ-pos t δ p q)
        ψ↑ p q = ψ (μₒ-pos t δ p q)
        δ↑ p = μₒ (δ p) (ϕ↑ p)
        ε↑ p = γₒ (Typₒ t p) (δ p) (ε p) (ϕ↑ p) (ψ↑ p)
    in nd o t δ↑ ε↑ 

  γₒ-pos-inl o .(μₒ t δ) (nd .o t δ ε) ϕ ψ (inl unit) = inl unit
  γₒ-pos-inl o .(μₒ t δ) (nd .o t δ ε) ϕ ψ (inr (p , q)) = 
    let ϕ↑ p q = ϕ (μₒ-pos t δ p q)
        ψ↑ p q = ψ (μₒ-pos t δ p q)
        δ↑ p = μₒ (δ p) (ϕ↑ p)
        ε↑ p = γₒ (Typₒ t p) (δ p) (ε p) (ϕ↑ p) (ψ↑ p)
    in inr (p , γₒ-pos-inl (Typₒ t p) (δ p) (ε p) (ϕ↑ p) (ψ↑ p) q)

  γₒ-pos-inr o .(ηₒ o) (lf .o) ϕ ψ p q =
    ηₒ-pos-elim o (λ p → Posₒ (ψ p) → Posₒ (ψ (ηₒ-pos o))) (λ p → p) p q
  γₒ-pos-inr o .(μₒ t δ) (nd .o t δ ε) ϕ ψ p q = 
    let ϕ↑ p q = ϕ (μₒ-pos t δ p q)
        ψ↑ p q = ψ (μₒ-pos t δ p q)
        δ↑ p = μₒ (δ p) (ϕ↑ p)
        ε↑ p = γₒ (Typₒ t p) (δ p) (ε p) (ϕ↑ p) (ψ↑ p)
        p₀ = μₒ-pos-fst t δ p
        p₁ = μₒ-pos-snd t δ p
    in inr (p₀ , γₒ-pos-inr (Typₒ t p₀) (δ p₀) (ε p₀) (ϕ↑ p₀) (ψ↑ p₀) p₁ q)

  γₒ-pos-elim o .(ηₒ o) (lf .o) ϕ ψ X inl* inr* p = inr* (ηₒ-pos o) p
  γₒ-pos-elim o .(μₒ t δ) (nd .o t δ ε) ϕ ψ X inl* inr* (inl unit) = inl* (inl unit)
  γₒ-pos-elim o .(μₒ t δ) (nd .o t δ ε) ϕ ψ X inl* inr* (inr (p , q)) = 
    let ϕ↑ p q = ϕ (μₒ-pos t δ p q)
        ψ↑ p q = ψ (μₒ-pos t δ p q)
        δ↑ p = μₒ (δ p) (ϕ↑ p)
        ε↑ p = γₒ (Typₒ t p) (δ p) (ε p) (ϕ↑ p) (ψ↑ p)
        X q = X (inr (p , q))
        inl* q = inl* (inr (p , q))
        inr* q r = inr* (μₒ-pos t δ p q) r
    in γₒ-pos-elim (Typₒ t p) (δ p) (ε p) (ϕ↑ p) (ψ↑ p) X inl* inr* q

  --
  --  Examples
  --

  ob : 𝕆 0
  ob = ●

  arrow : 𝕆 1
  arrow = ● ▸ arr

  2-drop : 𝕆 2
  2-drop = ● ▸ arr ▸ lf ●

  2-globe : 𝕆 2
  2-globe = ● ▸ arr ▸ nd ● arr (λ { unit → arr }) (λ { unit → lf ● })

  2-simplex : 𝕆 2
  2-simplex = ● ▸ arr ▸ nd ● arr (λ { unit → arr }) (λ { unit → nd ● arr (λ { unit → arr }) (λ { unit → lf ● }) })
