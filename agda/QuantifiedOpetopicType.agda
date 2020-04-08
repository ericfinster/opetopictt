{-# OPTIONS --without-K --rewriting #-}

open import Base
open import Opetopes

module QuantifiedOpetopicType where

  --
  --  Types
  --
  
  data Frm (A : Set) : {n : ℕ} (o : 𝕆 n) → Set
  data Tree (A : Set) : {n : ℕ} {o : 𝕆 n} (f : Frm A o) (t : 𝕋 o) → Set

  postulate

    Cell : (A : Set) {n : ℕ} {o : 𝕆 n} (f : Frm A o) → Set

  Typ : {A : Set} {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → {f : Frm A o} (σ : Tree A f t)
    → (p : Posₒ t)
    → Frm A (Typₒ t p)
  
  Inh : {A : Set} {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → {f : Frm A o} (σ : Tree A f t)
    → (p : Posₒ t)
    → Cell A (Typ σ p)

  data Frm A where
    ●_▸_ : (a₀ : A) (a₁ : A) → Frm A (○ ▹ arr)
    _∣_▸_ : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → (f : Frm A o) (σ : Tree A f t) (τ : Cell A f)
      → Frm A (o ▹ t)

  η : {A : Set} {n : ℕ} {o : 𝕆 n}
    → (f : Frm A o) (τ : Cell A f)
    → Tree A f (ηₒ o)

  μ : {A : Set} {n : ℕ} {o : 𝕆 n} {t : 𝕋 o} 
    → {δₒ : (p : Posₒ t) → 𝕋 (Typₒ t p)}
    → {f : Frm A o} (σ : Tree A f t)
    → (δ : (p : Posₒ t) → Tree A (Typ σ p) (δₒ p))
    → Tree A f (μₒ t δₒ)

  α : {A : Set} {a₀ a₁ a₂ : A}
    → {t₀ : 𝕋 (○ ▹ arr)} {t₁ : 𝕋 (○ ▹ arr)}
    → (σ₀ : Tree A (● a₀ ▸ a₁) t₀)
    → (σ₁ : Tree A (● a₁ ▸ a₂) t₁)
    → Tree A (● a₀ ▸ a₂) (γₒ ○ arr t₀ (λ _ → arr) (λ _ → t₁))

  γ : {A : Set} {n : ℕ} {o : 𝕆 n} {s : 𝕋 o} {t : 𝕋 (o ▹ s)}
    → {δₒ : (p : Posₒ s) → 𝕋 (Typₒ s p)}
    → {εₒ : (p : Posₒ s) → 𝕋 (Typₒ s p ▹ δₒ p)}
    → {f : Frm A o} (σ : Tree A f s) (τ : Cell A f)
    → (ρ : Tree A (f ∣ σ ▸ τ) t)
    → (δ : (p : Posₒ s) → Tree A (Typ σ p) (δₒ p))
    → (ε : (p : Posₒ s) → Tree A (Typ σ p ∣ δ p ▸ Inh σ p) (εₒ p))
    → Tree A (f ∣ μ σ δ ▸ τ) (γₒ o s t δₒ εₒ)

  data Tree A where

    nil : (a : A) → Tree A (● a ▸ a) (lfₒ ○)

    cns : {t : 𝕋 (○ ▹ arr)} {a₀ a₁ a₂ : A}
      → (ρ : Cell A (● a₀ ▸ a₁))
      → (θ : Tree A (● a₁ ▸ a₂) t)
      → Tree A (● a₀ ▸ a₂) (ndₒ ○ arr (λ _ → arr) (λ _ → t))

    lf : {n : ℕ} {o : 𝕆 n}
      → (f : Frm A o) (τ : Cell A f)
      → Tree A (f ∣ η f τ ▸ τ) (lfₒ o)

    nd : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o} 
      → {δₒ : (p : Posₒ t) → 𝕋 (Typₒ t p)}
      → {εₒ : (p : Posₒ t) → 𝕋 (Typₒ t p ▹ δₒ p)}
      → {f : Frm A o} (σ : Tree A f t) (τ : Cell A f)
      → (θ : Cell A (f ∣ σ ▸ τ))
      → (δ : (p : Posₒ t) → Tree A (Typ σ p) (δₒ p))
      → (ε : (p : Posₒ t) → Tree A (Typ σ p ∣ δ p ▸ Inh σ p) (εₒ p))
      → Tree A (f ∣ μ σ δ ▸ τ) (ndₒ o t δₒ εₒ)

  Typ (cns {a₀ = a₀} {a₁ = a₁} ρ σ) (inl unit) = ● a₀ ▸ a₁
  Typ (cns ρ σ) (inr (_ , q)) = Typ σ q
  Typ (nd σ τ θ δ ε) (inl unit) = _ ∣ σ ▸ τ
  Typ (nd σ τ θ δ ε) (inr (p , q)) = Typ (ε p) q
  
  Inh (cns ρ σ) (inl unit) = ρ
  Inh (cns ρ σ) (inr (p , q)) = Inh σ q
  Inh (nd σ τ θ δ ε) (inl unit) = θ
  Inh (nd σ τ θ δ ε) (inr (p , q)) = Inh (ε p) q

  postulate

    -- Typ/Inh laws
    η-pos-typ : {A : Set} {n : ℕ} {o : 𝕆 n}
      → (f : Frm A o) (τ : Cell A f)
      → Typ (η f τ) (ηₒ-pos o) ↦ f
    {-# REWRITE η-pos-typ #-}

    η-pos-inh : {A : Set} {n : ℕ} {o : 𝕆 n}
      → (f : Frm A o) (τ : Cell A f)
      → Inh (η f τ) (ηₒ-pos o) ↦ τ 
    {-# REWRITE η-pos-inh #-}

    μ-pos-typ : {A : Set} {n : ℕ} {o : 𝕆 n} {t : 𝕋 o} 
      → {δₒ : (p : Posₒ t) → 𝕋 (Typₒ t p)}
      → {f : Frm A o} (σ : Tree A f t)
      → (δ : (p : Posₒ t) → Tree A (Typ σ p) (δₒ p))
      → (p : Posₒ (μₒ t δₒ))
      → Typ (μ σ δ) p ↦ Typ (δ (μₒ-pos-fst t δₒ p)) (μₒ-pos-snd t δₒ p)
    {-# REWRITE μ-pos-typ #-}

    μ-pos-inh : {A : Set} {n : ℕ} {o : 𝕆 n} {t : 𝕋 o} 
      → {δₒ : (p : Posₒ t) → 𝕋 (Typₒ t p)}
      → {f : Frm A o} (σ : Tree A f t)
      → (δ : (p : Posₒ t) → Tree A (Typ σ p) (δₒ p))
      → (p : Posₒ (μₒ t δₒ))
      → Inh (μ σ δ) p ↦ Inh (δ (μₒ-pos-fst t δₒ p)) (μₒ-pos-snd t δₒ p)
    {-# REWRITE μ-pos-inh #-}

    -- μ laws
    μ-unit-right : {A : Set} {n : ℕ} {o : 𝕆 n} {t : 𝕋 o} 
      → {f : Frm A o} (σ : Tree A f t)
      → μ σ (λ p → η (Typ σ p) (Inh σ p)) ↦ σ
    {-# REWRITE μ-unit-right #-}

    μ-unit-left : {A : Set} {n : ℕ} {o : 𝕆 n}
      → {δₒ : (p : Posₒ (ηₒ o)) → 𝕋 o}
      → {f : Frm A o} {τ : Cell A f}
      → (δ : (p : Posₒ (ηₒ o)) → Tree A (Typ (η f τ) p) (δₒ p))
      → μ (η f τ) δ ↦ δ (ηₒ-pos o)
    {-# REWRITE μ-unit-left #-}

    μ-assoc : {A : Set} {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
      → {δₒ : (p : Posₒ t) → 𝕋 (Typₒ t p)}
      → {εₒ : (p : Posₒ (μₒ t δₒ)) → 𝕋 (Typₒ (μₒ t δₒ) p)}
      → {f : Frm A o} (σ : Tree A f t)
      → (δ : (p : Posₒ t) → Tree A (Typ σ p) (δₒ p))
      → (ε : (p : Posₒ (μₒ t δₒ)) → Tree A (Typ (μ σ δ) p) (εₒ p))
      → μ (μ σ δ) ε ↦ μ σ (λ p → μ (δ p) (λ q → ε (μₒ-pos t δₒ p q)))
    {-# REWRITE μ-assoc #-}

  η (● a₀ ▸ a₁) τ = cns τ (nil a₁)
  η (f ∣ σ ▸ τ) θ = 
    let η-dec p = η (Typ σ p) (Inh σ p)
        lf-dec p = lf (Typ σ p) (Inh σ p)
    in nd σ τ θ η-dec lf-dec

  μ (nil a) κ = nil a
  μ (cns ρ σ) κ = 
    let w = κ (inl unit)
        κ↑ p = κ (inr (unit , p))
    in α w (μ σ κ↑)
  μ (lf f τ) κ = lf f τ
  μ (nd σ τ θ δ ε) κ =
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μ (ε p) (κ↑ p) 
    in γ σ τ w δ ψ

  α (nil _) σ₁ = σ₁
  α (cns ρ σ₀) σ₁ = cns ρ (α σ₀ σ₁)

  γ {o = o} .(η f τ) .τ (lf f τ) ϕ ψ = ψ (ηₒ-pos o)
  γ {t = ndₒ o t δₒ εₒ} .(μ σ δ) .τ (nd σ τ θ δ ε) ϕ ψ = 
    let ϕ↑ p q = ϕ (μₒ-pos t δₒ p q)
        ψ↑ p q = ψ (μₒ-pos t δₒ p q)
        δ↑ p = μ (δ p) (ϕ↑ p)
        ε↑ p = γ (δ p) (Inh σ p) (ε p) (ϕ↑ p) (ψ↑ p)
    in nd σ τ θ δ↑ ε↑
    
  --
  --  Terms
  --

  Id-frm : {A : Set} (a : A)
    → {n : ℕ} (o : 𝕆 (S n))
    → Frm A o

  Id-tr : {A : Set} (a : A)
    → {n : ℕ} {o : 𝕆 (S n)} (t : 𝕋 o)
    → Tree A (Id-frm a o) t

  postulate

    Id-cell : {A : Set} (a : A)
      → {n : ℕ} (o : 𝕆 (S n))
      → Cell A (Id-frm a o)

  Id-frm a (○ ▹ arr) = ● a ▸ a
  Id-frm a (o ▹ s ▹ t) = Id-frm a (o ▹ s) ∣
    Id-tr a t ▸ Id-cell a (o ▹ s)
  
  Id-tr a (lfₒ ○) = nil a
  Id-tr a (ndₒ ○ arr δ ε) = {!!}
  Id-tr a (lfₒ (o ▹ t)) = {!lf!}
  Id-tr a (ndₒ (o ▹ s) t δ ε) = {!!}

  -- Tree-id a (○ ▹ arr) = η (● a ▸ a) (Cell-id a (○ ▹ arr))
  -- Tree-id a (o ▹ .(ηₒ o) ▹ lfₒ .o) =
  --   lf (Frm-id a (o ▹ ηₒ o)) (Cell-id a (o ▹ ηₒ o))
  -- Tree-id a (o ▹ .(μₒ t δ) ▹ ndₒ .o t δ ε) =
  --   let f-id = Frm-id a (o ▹ μₒ t δ)
  --       σ-id = Tree-id a (o ▹ μₒ t δ)
  --       τ-id = Cell-id a (o ▹ μₒ t δ)
  --       θ-id = Cell-id a (o ▹ μₒ t δ ▹ ndₒ o t δ ε)
  --   in {!nd f-id σ-id τ-id θ-id   !}

