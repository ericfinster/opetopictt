{-# OPTIONS --without-K --rewriting #-}

open import Base
open import Opetopes

module OpetopicType where

  --
  --  Types
  --
  
  data Frm (A : Set) : {n : ℕ} (o : 𝕆 n) → Set
  data Tree (A : Set) : {n : ℕ} {o : 𝕆 n} (f : Frm A o) (t : 𝕋 o) → Set

  postulate

    Cell : (A : Set) {n : ℕ} {o : 𝕆 n} (f : Frm A o) → Set

  Typ : {A : Set} {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → {f : Frm A o} (σ : Tree A f t)
    → (p : Pos t)
    → Frm A (Typₒ t p)
  
  Inh : {A : Set} {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → {f : Frm A o} (σ : Tree A f t)
    → (p : Pos t)
    → Cell A (Typ σ p)

  infixl 40 _∥_▹_

  data Frm A where
    □_▹_ : (a₀ : A) (a₁ : A) → Frm A ○
    _∥_▹_ : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → (f : Frm A o) (σ : Tree A f t) (τ : Cell A f)
      → Frm A (o ∣ t)

  η : {A : Set} {n : ℕ} {o : 𝕆 n}
    → (f : Frm A o) (τ : Cell A f)
    → Tree A f (ηₒ o)

  μ : {A : Set} {n : ℕ} {o : 𝕆 n} {t : 𝕋 o} 
    → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
    → {f : Frm A o} (σ : Tree A f t)
    → (δ : (p : Pos t) → Tree A (Typ σ p) (δₒ p))
    → Tree A f (μₒ t δₒ)

  α : {A : Set} {a₀ a₁ a₂ : A}
    → {t₀ : 𝕋 ○} {t₁ : 𝕋 ○}
    → (σ₀ : Tree A (□ a₀ ▹ a₁) t₀)
    → (σ₁ : Tree A (□ a₁ ▹ a₂) t₁)
    → Tree A (□ a₀ ▹ a₂) (αₒ t₀ t₁)

  γ : {A : Set} {n : ℕ} {o : 𝕆 n} {s : 𝕋 o} {t : 𝕋 (o ∣ s)}
    → {δₒ : (p : Pos s) → 𝕋 (Typₒ s p)}
    → {εₒ : (p : Pos s) → 𝕋 (Typₒ s p ∣ δₒ p)}
    → {f : Frm A o} (σ : Tree A f s) (τ : Cell A f)
    → (ρ : Tree A (f ∥ σ ▹ τ) t)
    → (δ : (p : Pos s) → Tree A (Typ σ p) (δₒ p))
    → (ε : (p : Pos s) → Tree A (Typ σ p ∥ δ p ▹ Inh σ p) (εₒ p))
    → Tree A (f ∥ μ σ δ ▹ τ) (γₒ o s t δₒ εₒ)

  data Tree A where

    nil : (a : A) → Tree A (□ a ▹ a) nilₒ

    cns : {t : 𝕋 ○} {a₀ a₁ a₂ : A}
      → (ρ : Cell A (□ a₀ ▹ a₁))
      → (θ : Tree A (□ a₁ ▹ a₂) t)
      → Tree A (□ a₀ ▹ a₂) (cnsₒ t)

    lf : {n : ℕ} {o : 𝕆 n}
      → (f : Frm A o) (τ : Cell A f)
      → Tree A (f ∥ η f τ ▹ τ) (lfₒ o)

    nd : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o} 
      → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
      → {εₒ : (p : Pos t) → 𝕋 (Typₒ t p ∣ δₒ p)}
      → {f : Frm A o} (σ : Tree A f t) (τ : Cell A f)
      → (θ : Cell A (f ∥ σ ▹ τ))
      → (δ : (p : Pos t) → Tree A (Typ σ p) (δₒ p))
      → (ε : (p : Pos t) → Tree A (Typ σ p ∥ δ p ▹ Inh σ p) (εₒ p))
      → Tree A (f ∥ μ σ δ ▹ τ) (ndₒ o t δₒ εₒ)

  Typ (cns {a₀ = a₀} {a₁ = a₁} ρ σ) (inl unit) = □ a₀ ▹ a₁
  Typ (cns ρ σ) (inr p) = Typ σ p
  Typ (nd σ τ θ δ ε) (inl unit) = _ ∥ σ ▹ τ
  Typ (nd σ τ θ δ ε) (inr (p , q)) = Typ (ε p) q

  Inh (cns ρ σ) (inl unit) = ρ
  Inh (cns ρ σ) (inr p) = Inh σ p
  Inh (nd σ τ θ δ ε) (inl unit) = θ
  Inh (nd σ τ θ δ ε) (inr (p , q)) = Inh (ε p) q

  postulate

    -- Typ/Inh laws
    η-pos-typ : {A : Set} {n : ℕ} {o : 𝕆 n}
      → (f : Frm A o) (τ : Cell A f)
      → (p : Pos (ηₒ o))
      → Typ (η f τ) p ↦ f
    {-# REWRITE η-pos-typ #-}

    η-pos-inh : {A : Set} {n : ℕ} {o : 𝕆 n}
      → (f : Frm A o) (τ : Cell A f)
      → (p : Pos (ηₒ o))
      → Inh (η f τ) p ↦ τ 
    {-# REWRITE η-pos-inh #-}

    μ-pos-typ : {A : Set} {n : ℕ} {o : 𝕆 n} {t : 𝕋 o} 
      → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
      → {f : Frm A o} (σ : Tree A f t)
      → (δ : (p : Pos t) → Tree A (Typ σ p) (δₒ p))
      → (p : Pos (μₒ t δₒ))
      → Typ (μ σ δ) p ↦ Typ (δ (μₒ-pos-fst t δₒ p)) (μₒ-pos-snd t δₒ p)
    {-# REWRITE μ-pos-typ #-}

    μ-pos-inh : {A : Set} {n : ℕ} {o : 𝕆 n} {t : 𝕋 o} 
      → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
      → {f : Frm A o} (σ : Tree A f t)
      → (δ : (p : Pos t) → Tree A (Typ σ p) (δₒ p))
      → (p : Pos (μₒ t δₒ))
      → Inh (μ σ δ) p ↦ Inh (δ (μₒ-pos-fst t δₒ p)) (μₒ-pos-snd t δₒ p)
    {-# REWRITE μ-pos-inh #-}

    -- μ laws
    μ-unit-right : {A : Set} {n : ℕ} {o : 𝕆 n} {t : 𝕋 o} 
      → {f : Frm A o} (σ : Tree A f t)
      → μ σ (λ p → η (Typ σ p) (Inh σ p)) ↦ σ
    {-# REWRITE μ-unit-right #-}

    μ-unit-left : {A : Set} {n : ℕ} {o : 𝕆 n}
      → {δₒ : (p : Pos (ηₒ o)) → 𝕋 o}
      → {f : Frm A o} {τ : Cell A f}
      → (δ : (p : Pos (ηₒ o)) → Tree A (Typ (η f τ) p) (δₒ p))
      → μ (η f τ) δ ↦ δ (ηₒ-pos o)
    {-# REWRITE μ-unit-left #-}

    μ-assoc : {A : Set} {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
      → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
      → {εₒ : (p : Pos (μₒ t δₒ)) → 𝕋 (Typₒ (μₒ t δₒ) p)}
      → {f : Frm A o} (σ : Tree A f t)
      → (δ : (p : Pos t) → Tree A (Typ σ p) (δₒ p))
      → (ε : (p : Pos (μₒ t δₒ)) → Tree A (Typ (μ σ δ) p) (εₒ p))
      → μ (μ σ δ) ε ↦ μ σ (λ p → μ (δ p) (λ q → ε (μₒ-pos t δₒ p q)))
    {-# REWRITE μ-assoc #-}


  η (□ a₀ ▹ a₁) τ = cns τ (nil a₁)
  η (f ∥ σ ▹ τ) θ = 
    let η-dec p = η (Typ σ p) (Inh σ p)
        lf-dec p = lf (Typ σ p) (Inh σ p)
    in nd σ τ θ η-dec lf-dec

  μ (nil a) κ = nil a
  μ (cns ρ σ) κ = 
    let w = κ (inl unit)
        κ↑ p = κ (inr p)
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
    → {n : ℕ} (o : 𝕆 n)
    → Frm A o

  Id-tr : {A : Set} (a : A)
    → {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
    → Tree A (Id-frm a o) t

  postulate

    Id-cell : {A : Set} (a : A)
      → {n : ℕ} (o : 𝕆 n)
      → Cell A (Id-frm a o)

    Id-tr-η : {A : Set} (a : A)
      → {n : ℕ} (o : 𝕆 n)
      → Id-tr a (ηₒ o) ↦ η (Id-frm a o) (Id-cell a o)
    {-# REWRITE Id-tr-η #-}

    Id-tr-typ : {A : Set} (a : A)
      → {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
      → (p : Pos t)
      → Typ (Id-tr a t) p ↦ Id-frm a (Typₒ t p)
    {-# REWRITE Id-tr-typ #-}
    
    Id-tr-inh : {A : Set} (a : A)
      → {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
      → (p : Pos t)
      → Inh (Id-tr a t) p ↦ Id-cell a (Typₒ t p)
    {-# REWRITE Id-tr-inh #-}
    
    Id-tr-μ : {A : Set} (a : A)
      → {n : ℕ} {o : 𝕆 n} (t : 𝕋 o)
      → (κ : (p : Pos t) → 𝕋 (Typₒ t p))
      → Id-tr a (μₒ t κ) ↦ μ (Id-tr a t) (λ p → Id-tr a (κ p))
    {-# REWRITE Id-tr-μ #-}
    
  Id-frm a ○ = □ a ▹ a
  Id-frm a (o ∣ t) = Id-frm a o ∥ Id-tr a t ▹ Id-cell a o

  Id-tr a nilₒ = nil a
  Id-tr a (cnsₒ t) = cns (Id-cell a ○) (Id-tr a t)
  Id-tr a (lfₒ o) = lf (Id-frm a o) (Id-cell a o)
  Id-tr a (ndₒ o t δ ε) =
    nd (Id-tr a t) (Id-cell a o) (Id-cell a (o ∣ t))
       (λ p → Id-tr a (δ p))
       (λ p → Id-tr a (ε p))


