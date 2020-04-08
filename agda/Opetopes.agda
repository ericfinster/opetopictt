{-# OPTIONS --without-K --rewriting #-}

open import Base

module Opetopes where

  data 𝕆 : ℕ → Set
  data 𝕋 : {n : ℕ} → 𝕆 n → Set
  
  Pos : {n : ℕ} {o : 𝕆 n} → 𝕋 o → Set
  Typₒ : {n : ℕ} {o : 𝕆 n}
    → (t : 𝕋 o) (p : Pos t)
    → 𝕆 n 

  infixl 40 _∣_
  
  data 𝕆 where
    □ : 𝕆 O
    _∣_ : {n : ℕ} (o : 𝕆 n) (t : 𝕋 o) → 𝕆 (S n)

  ηₒ : {n : ℕ} (o : 𝕆 n) → 𝕋 o

  ηₒ-pos : {n : ℕ} (o : 𝕆 n)
    → Pos (ηₒ o)

  ηₒ-pos-elim : {n : ℕ} (o : 𝕆 n)
    → (X : (p : Pos (ηₒ o)) → Set)
    → (η-pos* : X (ηₒ-pos o))
    → (p : Pos (ηₒ o)) → X p

  μₒ : {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
    → (κ : (p : Pos t) → 𝕋 (Typₒ t p))
    → 𝕋 o

  μₒ-pos : {n : ℕ} {o : 𝕆 n} (o : 𝕋 o)
    → (κ : (p : Pos o) → 𝕋 (Typₒ o p))
    → (p : Pos o) (t : Pos (κ p))
    → Pos (μₒ o κ)

  μₒ-pos-fst : {n : ℕ} {o : 𝕆 n} (o : 𝕋 o)
    → (κ : (p : Pos o) → 𝕋 (Typₒ o p))
    → Pos (μₒ o κ) → Pos o

  μₒ-pos-snd : {n : ℕ} {o : 𝕆 n} (o : 𝕋 o)
    → (κ : (p : Pos o) → 𝕋 (Typₒ o p))
    → (p : Pos (μₒ o κ)) → Pos (κ (μₒ-pos-fst o κ p))

  αₒ : 𝕋 □ → 𝕋 □ → 𝕋 □ 

  αₒ-pos-inl : {t₀ : 𝕋 □} {t₁ : 𝕋 □}
    → Pos t₀ → Pos (αₒ t₀ t₁)

  αₒ-pos-inr : {t₀ : 𝕋 □} {t₁ : 𝕋 □}
    → Pos t₁ → Pos (αₒ t₀ t₁)

  αₒ-pos-elim : (t₀ : 𝕋 □) (t₁ : 𝕋 □)
    → (X : Pos (αₒ t₀ t₁) → Set)
    → (inl* : (p : Pos t₀) → X (αₒ-pos-inl p))
    → (inr* : (p : Pos t₁) → X (αₒ-pos-inr p))
    → (p : Pos (αₒ t₀ t₁)) → X p

  γₒ : {n : ℕ} (o : 𝕆 n) (s : 𝕋 o) (t : 𝕋 (o ∣ s))
    → (δ : (p : Pos s) → 𝕋 (Typₒ s p))
    → (ε : (p : Pos s) → 𝕋 (Typₒ s p ∣ δ p))
    → 𝕋 (o ∣ μₒ s δ)

  γₒ-pos-inl : {n : ℕ} (o : 𝕆 n) (s : 𝕋 o) (t : 𝕋 (o ∣ s))
    → (δ : (p : Pos s) → 𝕋 (Typₒ s p))
    → (ε : (p : Pos s) → 𝕋 (Typₒ s p ∣ δ p))
    → Pos t → Pos (γₒ o s t δ ε)

  γₒ-pos-inr : {n : ℕ} (o : 𝕆 n) (s : 𝕋 o) (t : 𝕋 (o ∣ s))
    → (δ : (p : Pos s) → 𝕋 (Typₒ s p))
    → (ε : (p : Pos s) → 𝕋 (Typₒ s p ∣ δ p))
    → (p : Pos s) (q : Pos (ε p))
    → Pos (γₒ o s t δ ε)

  γₒ-pos-elim : {n : ℕ} (o : 𝕆 n) (s : 𝕋 o) (t : 𝕋 (o ∣ s))
    → (δ : (p : Pos s) → 𝕋 (Typₒ s p))
    → (ε : (p : Pos s) → 𝕋 (Typₒ s p ∣ δ p))
    → (X : Pos (γₒ o s t δ ε) → Set)
    → (inl* : (p : Pos t) → X (γₒ-pos-inl o s t δ ε p))
    → (inr* : (p : Pos s) (q : Pos (ε p)) → X (γₒ-pos-inr o s t δ ε p q))
    → (p : Pos (γₒ o s t δ ε)) → X p

  data 𝕋 where

    nilₒ : 𝕋 □ 
    cnsₒ : 𝕋 □ → 𝕋 □ 
    
    lfₒ : {n : ℕ} (o : 𝕆 n) → 𝕋 (o ∣ ηₒ o)
    ndₒ : {n : ℕ} (o : 𝕆 n) (t : 𝕋 o)
      → (δ : (p : Pos t) → 𝕋 (Typₒ t p))
      → (ε : (p : Pos t) → 𝕋 (Typₒ t p ∣ δ p))
      → 𝕋 (o ∣ μₒ t δ)

  Pos nilₒ = ⊥
  Pos (cnsₒ t) = ⊤ ⊔ Pos t
  Pos (lfₒ o) = ⊥
  Pos (ndₒ o t δ ε) = ⊤ ⊔ Σ (Pos t) (λ p → Pos (ε p))

  Typₒ (cnsₒ t) (inl unit) = □
  Typₒ (cnsₒ t) (inr p) = Typₒ t p
  Typₒ (ndₒ o t δ ε) (inl unit) = o ∣ t
  Typₒ (ndₒ o t δ ε) (inr (p , q)) = Typₒ (ε p) q

  postulate

    -- ηₒ-pos laws
    ηₒ-pos-typ : {n : ℕ} (o : 𝕆 n)
      → (p : Pos (ηₒ o))
      → Typₒ (ηₒ o) p ↦ o
    {-# REWRITE ηₒ-pos-typ #-}

    ηₒ-pos-elim-β : {n : ℕ} (o : 𝕆 n)
      → (X : (p : Pos (ηₒ o)) → Set)
      → (ηₒ-pos* : X (ηₒ-pos o))
      → ηₒ-pos-elim o X ηₒ-pos* (ηₒ-pos o) ↦ ηₒ-pos*
    {-# REWRITE ηₒ-pos-elim-β #-}

    -- μₒ-pos laws
    μₒ-pos-typ : {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
      → (κ : (p : Pos t) → 𝕋 (Typₒ t p))
      → (p : Pos (μₒ t κ))
      → Typₒ (μₒ t κ) p ↦ Typₒ (κ (μₒ-pos-fst t κ p)) (μₒ-pos-snd t κ p)
    {-# REWRITE μₒ-pos-typ #-}
  
    μₒ-pos-fst-β : {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
      → (κ : (p : Pos t) → 𝕋 (Typₒ t p))
      → (p : Pos t) (q : Pos (κ p))
      → μₒ-pos-fst t κ (μₒ-pos t κ p q) ↦ p
    {-# REWRITE μₒ-pos-fst-β #-}

    μₒ-pos-snd-β : {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
      → (κ : (p : Pos t) → 𝕋 (Typₒ t p))
      → (p : Pos t) (q : Pos (κ p))
      → μₒ-pos-snd t κ (μₒ-pos t κ p q) ↦ q
    {-# REWRITE μₒ-pos-snd-β #-}
    
    μₒ-pos-η : {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
      → (κ : (p : Pos t) → 𝕋 (Typₒ t p))
      → (p : Pos (μₒ t κ))
      → μₒ-pos t κ (μₒ-pos-fst t κ p) (μₒ-pos-snd t κ p) ↦ p
    {-# REWRITE μₒ-pos-η #-}

    -- μₒ laws
    μₒ-unit-r : {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
      → μₒ t (λ p → ηₒ (Typₒ t p)) ↦ t
    {-# REWRITE μₒ-unit-r #-}

    μₒ-unit-l : {n : ℕ} {o : 𝕆 n} (ϕ : (p : Pos (ηₒ o)) → 𝕋 o)
      → μₒ (ηₒ o) ϕ ↦ ϕ (ηₒ-pos o)
    {-# REWRITE μₒ-unit-l #-}

    μₒ-assoc : {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
      → (κ : (p : Pos t) → 𝕋 (Typₒ t p))
      → (θ : (p : Pos (μₒ t κ)) → 𝕋 (Typₒ (μₒ t κ) p))
      → μₒ (μₒ t κ) θ ↦ μₒ t (λ p → μₒ (κ p) (λ q → θ (μₒ-pos t κ p q)))
    {-# REWRITE μₒ-assoc #-}

    -- αₒ elim rules
    αₒ-pos-elim-inl-β : (t₀ : 𝕋 □) (t₁ : 𝕋 □)
      → (X : Pos (αₒ t₀ t₁) → Set)
      → (inl* : (p : Pos t₀) → X (αₒ-pos-inl p))
      → (inr* : (p : Pos t₁) → X (αₒ-pos-inr p))
      → (p : Pos t₀)
      → αₒ-pos-elim t₀ t₁ X inl* inr* (αₒ-pos-inl p) ↦ inl* p
    {-# REWRITE αₒ-pos-elim-inl-β #-}

    αₒ-pos-elim-inr-β : (t₀ : 𝕋 □) (t₁ : 𝕋 □)
      → (X : Pos (αₒ t₀ t₁) → Set)
      → (inl* : (p : Pos t₀) → X (αₒ-pos-inl p))
      → (inr* : (p : Pos t₁) → X (αₒ-pos-inr p))
      → (p : Pos t₁)
      → αₒ-pos-elim t₀ t₁ X inl* inr* (αₒ-pos-inr p) ↦ inr* p
    {-# REWRITE αₒ-pos-elim-inr-β #-}

    -- γₒ elim rules
    γₒ-pos-elim-inl-β : {n : ℕ} (o : 𝕆 n) (s : 𝕋 o) (t : 𝕋 (o ∣ s))
      → (δ : (p : Pos s) → 𝕋 (Typₒ s p))
      → (ε : (p : Pos s) → 𝕋 (Typₒ s p ∣ δ p))
      → (X : Pos (γₒ o s t δ ε) → Set)
      → (inl* : (p : Pos t) → X (γₒ-pos-inl o s t δ ε p))
      → (inr* : (p : Pos s) (q : Pos (ε p)) → X (γₒ-pos-inr o s t δ ε p q))
      → (p : Pos t)
      → γₒ-pos-elim o s t δ ε X inl* inr* (γₒ-pos-inl o s t δ ε p) ↦ inl* p
    {-# REWRITE γₒ-pos-elim-inl-β #-}

    γₒ-pos-elim-inr-β : {n : ℕ} (o : 𝕆 n) (s : 𝕋 o) (t : 𝕋 (o ∣ s))
      → (δ : (p : Pos s) → 𝕋 (Typₒ s p))
      → (ε : (p : Pos s) → 𝕋 (Typₒ s p ∣ δ p))
      → (X : Pos (γₒ o s t δ ε) → Set)
      → (inl* : (p : Pos t) → X (γₒ-pos-inl o s t δ ε p))
      → (inr* : (p : Pos s) (q : Pos (ε p)) → X (γₒ-pos-inr o s t δ ε p q))
      → (p : Pos s) (q : Pos (ε p))
      → γₒ-pos-elim o s t δ ε X inl* inr* (γₒ-pos-inr o s t δ ε p q) ↦ inr* p q
    {-# REWRITE γₒ-pos-elim-inr-β #-}

  ηₒ □ = cnsₒ nilₒ
  ηₒ (o ∣ t) =
    let η-dec p = ηₒ (Typₒ t p)
        lfₒ-dec p = lfₒ (Typₒ t p)
    in ndₒ o t η-dec lfₒ-dec

  ηₒ-pos □ = inl unit
  ηₒ-pos (o ∣ t) = inl unit

  ηₒ-pos-elim □ X η-pos* (inl unit) = η-pos*
  ηₒ-pos-elim (o ∣ t) X η-pos* (inl unit) = η-pos*

  μₒ nilₒ κ = nilₒ
  μₒ (cnsₒ t) κ = 
    let w = κ (inl unit)
        κ↑ p = κ (inr p)
    in αₒ w (μₒ t κ↑)
  μₒ (lfₒ o) κ = lfₒ o
  μₒ (ndₒ o t δ ε) κ = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ϕ p = μₒ (ε p) (κ↑ p)
    in γₒ o t w δ ϕ

  μₒ-pos (cnsₒ t) κ (inl unit) q = 
    let w = κ (inl unit)
        κ↑ p = κ (inr p)
    in αₒ-pos-inl q
  μₒ-pos (cnsₒ t) κ (inr p) q = 
    let w = κ (inl unit)
        κ↑ p = κ (inr p)
    in αₒ-pos-inr (μₒ-pos t κ↑ p q)
  μₒ-pos (ndₒ o t δ ε) κ (inl unit) r = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ϕ p = μₒ (ε p) (κ↑ p)
    in γₒ-pos-inl o t w δ ϕ r 
  μₒ-pos (ndₒ o t δ ε) κ (inr (p , q)) r = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ϕ p = μₒ (ε p) (κ↑ p)
    in γₒ-pos-inr o t w δ ϕ p (μₒ-pos (ε p) (κ↑ p) q r)

  μₒ-pos-fst (cnsₒ t) κ p = 
    let w = κ (inl unit)
        κ↑ p = κ (inr p)
        X _ = ⊤ ⊔ Pos t
        inl* p = inl unit
        inr* p = inr (μₒ-pos-fst t κ↑ p)
    in αₒ-pos-elim w (μₒ t κ↑) X inl* inr* p
  μₒ-pos-fst (ndₒ o t δ ε) κ p =
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ϕ p = μₒ (ε p) (κ↑ p)
        X _ = ⊤ ⊔ Σ (Pos t) (λ q → Pos (ε q))
        inl* p = inl unit
        inr* p q = inr (p , (μₒ-pos-fst (ε p) (κ↑ p) q))
    in γₒ-pos-elim o t w δ ϕ X inl* inr* p

  μₒ-pos-snd (cnsₒ t) κ p = 
    let w = κ (inl unit)
        κ↑ p = κ (inr p)
        X p = Pos (κ (μₒ-pos-fst (cnsₒ t) κ p))
        inl* p = p
        inr* p = μₒ-pos-snd t κ↑ p
    in αₒ-pos-elim w (μₒ t κ↑) X inl* inr* p
  μₒ-pos-snd (ndₒ o t δ ε) κ p = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ϕ p = μₒ (ε p) (κ↑ p)
        X p = Pos (κ (μₒ-pos-fst (ndₒ o t δ ε) κ p))
        inl* p = p
        inr* p q = μₒ-pos-snd (ε p) (κ↑ p) q
    in γₒ-pos-elim o t w δ ϕ X inl* inr* p

  αₒ nilₒ t₁ = t₁
  αₒ (cnsₒ t₀) t₁ = cnsₒ (αₒ t₀ t₁)
  
  αₒ-pos-inl {t₀ = cnsₒ t₀} (inl unit) = inl unit
  αₒ-pos-inl {t₀ = cnsₒ t₀} (inr p) = inr (αₒ-pos-inl p)
  
  αₒ-pos-inr {t₀ = nilₒ} p = p
  αₒ-pos-inr {t₀ = cnsₒ t₀} p = inr (αₒ-pos-inr p)
  
  αₒ-pos-elim nilₒ t₁ X inl* inr* p = inr* p
  αₒ-pos-elim (cnsₒ t₀) t₁ X inl* inr* (inl unit) = inl* (inl unit)
  αₒ-pos-elim (cnsₒ t₀) t₁ X inl* inr* (inr p) =
    αₒ-pos-elim t₀ t₁ (λ p → X (inr p)) (λ p → inl* (inr p)) inr* p

  γₒ o .(ηₒ o) (lfₒ .o) ϕ ψ = ψ (ηₒ-pos o)
  γₒ o .(μₒ t δ) (ndₒ .o t δ ε) ϕ ψ =
    let ϕ↑ p q = ϕ (μₒ-pos t δ p q)
        ψ↑ p q = ψ (μₒ-pos t δ p q)
        δ↑ p = μₒ (δ p) (ϕ↑ p)
        ε↑ p = γₒ (Typₒ t p) (δ p) (ε p) (ϕ↑ p) (ψ↑ p)
    in ndₒ o t δ↑ ε↑ 

  γₒ-pos-inl o .(μₒ t δ) (ndₒ .o t δ ε) ϕ ψ (inl unit) = inl unit
  γₒ-pos-inl o .(μₒ t δ) (ndₒ .o t δ ε) ϕ ψ (inr (p , q)) = 
    let ϕ↑ p q = ϕ (μₒ-pos t δ p q)
        ψ↑ p q = ψ (μₒ-pos t δ p q)
        δ↑ p = μₒ (δ p) (ϕ↑ p)
        ε↑ p = γₒ (Typₒ t p) (δ p) (ε p) (ϕ↑ p) (ψ↑ p)
    in inr (p , γₒ-pos-inl (Typₒ t p) (δ p) (ε p) (ϕ↑ p) (ψ↑ p) q)

  γₒ-pos-inr o .(ηₒ o) (lfₒ .o) ϕ ψ p q =
    ηₒ-pos-elim o (λ p → Pos (ψ p) → Pos (ψ (ηₒ-pos o))) (λ p → p) p q
  γₒ-pos-inr o .(μₒ t δ) (ndₒ .o t δ ε) ϕ ψ p q = 
    let ϕ↑ p q = ϕ (μₒ-pos t δ p q)
        ψ↑ p q = ψ (μₒ-pos t δ p q)
        δ↑ p = μₒ (δ p) (ϕ↑ p)
        ε↑ p = γₒ (Typₒ t p) (δ p) (ε p) (ϕ↑ p) (ψ↑ p)
        p₀ = μₒ-pos-fst t δ p
        p₁ = μₒ-pos-snd t δ p
    in inr (p₀ , γₒ-pos-inr (Typₒ t p₀) (δ p₀) (ε p₀) (ϕ↑ p₀) (ψ↑ p₀) p₁ q)

  γₒ-pos-elim o .(ηₒ o) (lfₒ .o) ϕ ψ X inl* inr* p = inr* (ηₒ-pos o) p
  γₒ-pos-elim o .(μₒ t δ) (ndₒ .o t δ ε) ϕ ψ X inl* inr* (inl unit) = inl* (inl unit)
  γₒ-pos-elim o .(μₒ t δ) (ndₒ .o t δ ε) ϕ ψ X inl* inr* (inr (p , q)) = 
    let ϕ↑ p q = ϕ (μₒ-pos t δ p q)
        ψ↑ p q = ψ (μₒ-pos t δ p q)
        δ↑ p = μₒ (δ p) (ϕ↑ p)
        ε↑ p = γₒ (Typₒ t p) (δ p) (ε p) (ϕ↑ p) (ψ↑ p)
        X q = X (inr (p , q))
        inl* q = inl* (inr (p , q))
        inr* q r = inr* (μₒ-pos t δ p q) r
    in γₒ-pos-elim (Typₒ t p) (δ p) (ε p) (ϕ↑ p) (ψ↑ p) X inl* inr* q

