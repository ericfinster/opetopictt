{-# OPTIONS --without-K --rewriting #-}

open import Base
open import Opetopes
open import OpetopicType

module OpetopicTypeOver where

  data Frm↓ (A : Set) (B : A → Set) :
    {n : ℕ} {o : 𝕆 n} (f : Frm A o) → Set
    
  data Tree↓ (A : Set) (B : A → Set) :
      {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → {f : Frm A o} (f↓ : Frm↓ A B f)
    → (σ : Tree A f t) → Set

  postulate

    Cell↓ : (A : Set) (B : A → Set)
      → {n : ℕ} {o : 𝕆 n} {f : Frm A o}
      → (f↓ : Frm↓ A B f) (τ : Cell A f)
      → Set

  Typ↓ : {A : Set} {B : A → Set}
    → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → {f : Frm A o} {σ : Tree A f t}
    → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ)
    → (p : Pos t)
    → Frm↓ A B (Typ σ p)
  
  Inh↓ : {A : Set} {B : A → Set}
    → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → {f : Frm A o} {σ : Tree A f t}
    → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ)
    → (p : Pos t)
    → Cell↓ A B (Typ↓ σ↓ p) (Inh σ p)

  infixl 30 _∥_▸_

  data Frm↓ A B where
    ■_▸_ : {a₀ a₁ : A}
      → (b₀ : B a₀) (b₁ : B a₁)
      → Frm↓ A B (□ a₀ ▹ a₁)
    _∥_▸_ : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm A o} (f↓ : Frm↓ A B f)
      → {σ : Tree A f t} (σ↓ : Tree↓ A B f↓ σ)
      → {τ : Cell A f} (τ↓ : Cell↓ A B f↓ τ)
      → Frm↓ A B (f ∥ σ ▹ τ)

  η↓ : {A : Set} {B : A → Set}
    → {n : ℕ} {o : 𝕆 n}
    → {f : Frm A o} {τ : Cell A f}
    → (f↓ : Frm↓ A B f)(τ↓ : Cell↓ A B f↓ τ)
    → Tree↓ A B f↓ (η f τ)
  
  μ↓ : {A : Set} {B : A → Set}
    → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
    → {f : Frm A o} {σ : Tree A f t}
    → {δ : (p : Pos t) → Tree A (Typ σ p) (δₒ p)}
    → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ)
    → (δ↓ : (p : Pos t) → Tree↓ A B (Typ↓ σ↓ p) (δ p))
    → Tree↓ A B f↓ (μ σ δ)
  
  α↓ : {A : Set} {B : A → Set}
    → {t₀ : 𝕋 ○} {t₁ : 𝕋 ○}
    → {a₀ : A} {a₁ : A} {a₂ : A} 
    → {σ₀ : Tree A (□ a₁ ▹ a₂) t₀} {σ₁ : Tree A (□ a₀ ▹ a₁) t₁}
    → {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂}
    → (σ↓₀ : Tree↓ A B (■ b₁ ▸ b₂) σ₀)
    → (σ↓₁ : Tree↓ A B (■ b₀ ▸ b₁) σ₁)
    → Tree↓ A B (■ b₀ ▸ b₂) (α σ₀ σ₁)
  
  γ↓ : {A : Set} {B : A → Set}
    → {n : ℕ} {o : 𝕆 n} {s : 𝕋 o} {t : 𝕋 (o ∣ s)}
    → {ϕₒ : (p : Pos s) → 𝕋 (Typₒ s p)}
    → {ψₒ : (p : Pos s) → 𝕋 (Typₒ s p ∣ ϕₒ p)}
    → {f : Frm A o} {σ : Tree A f s}
    → {τ : Cell A f} {ρ : Tree A (f ∥ σ ▹ τ) t}
    → {ϕ : (p : Pos s) → Tree A (Typ σ p) (ϕₒ p)}
    → {ψ : (p : Pos s) → Tree A (Typ σ p ∥ ϕ p ▹ Inh σ p) (ψₒ p)}
    → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ)
    → (τ↓ : Cell↓ A B f↓ τ) (ρ↓ : Tree↓ A B (f↓ ∥ σ↓ ▸ τ↓) ρ)
    → (ϕ↓ : (p : Pos s) → Tree↓ A B (Typ↓ σ↓ p) (ϕ p))
    → (ψ↓ : (p : Pos s) → Tree↓ A B (Typ↓ σ↓ p ∥ ϕ↓ p ▸ Inh↓ σ↓ p) (ψ p))
    → Tree↓ A B (f↓ ∥ μ↓ σ↓ ϕ↓ ▸ τ↓) (γ σ τ ρ ϕ ψ)

  data Tree↓ A B where
  
    nil↓ : {a : A} (b : B a)
      → Tree↓ A B (■ b ▸ b) (nil a)

    cns↓ : {t : 𝕋 ○} {a₀ : A} {a₁ : A} {a₂ : A}
      → {ρ : Cell A (□ a₁ ▹ a₂)} {θ : Tree A (□ a₀ ▹ a₁) t}
      → {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂}
      → (ρ↓ : Cell↓ A B (■ b₁ ▸ b₂) ρ)
      → (θ↓ : Tree↓ A B (■ b₀ ▸ b₁) θ)
      → Tree↓ A B (■ b₀ ▸ b₂) (cns ρ θ)

    lf↓ : {n : ℕ} {o : 𝕆 n}
      → {f : Frm A o} {τ : Cell A f}
      → (f↓ : Frm↓ A B f) (τ↓ : Cell↓ A B f↓ τ)
      → Tree↓ A B (f↓ ∥ η↓ f↓ τ↓ ▸ τ↓) (lf f τ)

    nd↓ : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
      → {εₒ : (p : Pos t) → 𝕋 (Typₒ t p ∣ δₒ p)}
      → {f : Frm A o} {σ : Tree A f t} {τ : Cell A f}
      → {θ : Cell A (f ∥ σ ▹ τ)}
      → {δ : (p : Pos t) → Tree A (Typ σ p) (δₒ p)}
      → {ε : (p : Pos t) → Tree A (Typ σ p ∥ δ p ▹ Inh σ p) (εₒ p)}
      → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ) (τ↓ : Cell↓ A B f↓ τ)
      → (θ↓ : Cell↓ A B (f↓ ∥ σ↓ ▸ τ↓) θ)
      → (δ↓ : (p : Pos t) → Tree↓ A B (Typ↓ σ↓ p) (δ p))
      → (ε↓ : (p : Pos t) → Tree↓ A B (Typ↓ σ↓ p ∥ δ↓ p ▸ Inh↓ σ↓ p) (ε p))
      → Tree↓ A B (f↓ ∥ μ↓ σ↓ δ↓ ▸ τ↓) (nd σ τ θ δ ε)

  Typ↓ (cns↓ {b₀ = b₀} {b₁ = b₁} {b₂ = b₂} ρ↓ σ↓) (inl unit) = ■ b₁ ▸ b₂
  Typ↓ (cns↓ ρ↓ θ↓) (inr p) = Typ↓ θ↓ p
  Typ↓ (nd↓ {f↓ = f↓} σ↓ τ↓ θ↓ δ↓ ε↓) (inl unit) = f↓ ∥ σ↓ ▸ τ↓
  Typ↓ (nd↓ σ↓ τ↓ θ↓ δ↓ ε↓) (inr (p , q)) = Typ↓ (ε↓ p) q

  Inh↓ (cns↓ ρ↓ θ↓) (inl unit) = ρ↓
  Inh↓ (cns↓ ρ↓ θ↓) (inr p) = Inh↓ θ↓ p
  Inh↓ (nd↓ σ↓ τ↓ θ↓ δ↓ ε↓) (inl unit) = θ↓
  Inh↓ (nd↓ σ↓ τ↓ θ↓ δ↓ ε↓) (inr (p , q)) = Inh↓ (ε↓ p) q

  postulate

    -- Typ/Inh laws
    η↓-pos-typ : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n}
      → {f : Frm A o} {τ : Cell A f}
      → (f↓ : Frm↓ A B f) (τ↓ : Cell↓ A B f↓ τ)
      → (p : Pos (ηₒ o))
      → Typ↓ (η↓ f↓ τ↓) p ↦ f↓
    {-# REWRITE η↓-pos-typ #-}

    η↓-pos-inh : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n}
      → {f : Frm A o} {τ : Cell A f}
      → (f↓ : Frm↓ A B f) (τ↓ : Cell↓ A B f↓ τ)
      → (p : Pos (ηₒ o))
      → Inh↓ (η↓ f↓ τ↓) p ↦ τ↓
    {-# REWRITE η↓-pos-inh #-}

    μ↓-pos-typ : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
      → {f : Frm A o} {σ : Tree A f t}
      → {δ : (p : Pos t) → Tree A (Typ σ p) (δₒ p)}
      → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ)
      → (δ↓ : (p : Pos t) → Tree↓ A B (Typ↓ σ↓ p) (δ p))
      → (p : Pos (μₒ t δₒ))
      → Typ↓ (μ↓ σ↓ δ↓) p ↦ Typ↓ (δ↓ (μₒ-pos-fst t δₒ p)) (μₒ-pos-snd t δₒ p)
    {-# REWRITE μ↓-pos-typ #-}

    μ↓-pos-inh : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
      → {f : Frm A o} {σ : Tree A f t}
      → {δ : (p : Pos t) → Tree A (Typ σ p) (δₒ p)}
      → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ)
      → (δ↓ : (p : Pos t) → Tree↓ A B (Typ↓ σ↓ p) (δ p))
      → (p : Pos (μₒ t δₒ))
      → Inh↓ (μ↓ σ↓ δ↓) p ↦ Inh↓ (δ↓ (μₒ-pos-fst t δₒ p)) (μₒ-pos-snd t δₒ p)
    {-# REWRITE μ↓-pos-inh #-}

    -- μ↓ laws
    μ↓-unit-r : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm A o} {σ : Tree A f t}
      → (f↓ : Frm↓ A B f) (σ↓ : Tree↓ A B f↓ σ)
      → μ↓ σ↓ (λ p → η↓ (Typ↓ σ↓ p) (Inh↓ σ↓ p)) ↦ σ↓
    {-# REWRITE μ↓-unit-r #-}

    μ↓-unit-l : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n}
      → (δₒ : (p : Pos (ηₒ o)) → 𝕋 o)      
      → {f : Frm A o} {τ : Cell A f}
      → {δ : (p : Pos (ηₒ o)) → Tree A (Typ (η f τ) p) (δₒ p)}
      → (f↓ : Frm↓ A B f) (τ↓ : Cell↓ A B f↓ τ)
      → (δ↓ : (p : Pos (ηₒ o)) → Tree↓ A B (Typ↓ (η↓ f↓ τ↓) p) (δ p))
      → μ↓ (η↓ f↓ τ↓) δ↓ ↦ δ↓ (ηₒ-pos o)
    {-# REWRITE μ↓-unit-l #-}
    
    μ↓-assoc : {A : Set} {B : A → Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → (δₒ : (p : Pos t) → 𝕋 (Typₒ t p))
      → (εₒ : (p : Pos (μₒ t δₒ)) → 𝕋 (Typₒ (μₒ t δₒ) p))
      → {f : Frm A o} {σ : Tree A f t}
      → {δ : (p : Pos t) → Tree A (Typ σ p) (δₒ p)}
      → {ε : (p : Pos (μₒ t δₒ)) → Tree A (Typ (μ σ δ) p) (εₒ p)}
      → (f↓ : Frm↓ A B f) (σ↓ : Tree↓ A B f↓ σ)
      → (δ↓ : (p : Pos t) → Tree↓ A B (Typ↓ σ↓ p) (δ p))
      → (ε↓ : (p : Pos (μₒ t δₒ)) → Tree↓ A B (Typ↓ (μ↓ σ↓ δ↓) p) (ε p))
      → μ↓ (μ↓ σ↓ δ↓) ε↓ ↦ μ↓ σ↓ (λ p → μ↓ (δ↓ p) (λ q →  ε↓ (μₒ-pos t δₒ p q)))
    {-# REWRITE μ↓-assoc #-}

  η↓ (■ b₀ ▸ b₁) τ↓ = cns↓ τ↓ (nil↓ b₀) 
  η↓ (f↓ ∥ σ↓ ▸ τ↓) θ↓ = 
    let η↓-dec p = η↓ (Typ↓ σ↓ p) (Inh↓ σ↓ p)
        lf↓-dec p = lf↓ (Typ↓ σ↓ p) (Inh↓ σ↓ p)
    in nd↓ σ↓ τ↓ θ↓ η↓-dec lf↓-dec 

  μ↓ (nil↓ b) κ↓ = nil↓ b
  μ↓ (cns↓ ρ↓ σ↓) κ↓ =
    let w↓ = κ↓ (inl unit)
        κ↓↑ p = κ↓ (inr p)
    in α↓ w↓ (μ↓ σ↓ κ↓↑)
  μ↓ (lf↓ f↓ τ↓) κ↓ = lf↓ f↓ τ↓
  μ↓ (nd↓ σ↓ τ↓ θ↓ δ↓ ε↓) κ↓ =
    let w↓ = κ↓ (inl unit)
        κ↓↑ p q = κ↓ (inr (p , q))
        ψ↓ p = μ↓ (ε↓ p) (κ↓↑ p)
    in γ↓ σ↓ τ↓ w↓ δ↓ ψ↓

  α↓ (nil↓ _) σ↓₁ = σ↓₁
  α↓ (cns↓ ρ↓ σ↓₀) σ↓₁ = cns↓ ρ↓ (α↓ σ↓₀ σ↓₁)

  γ↓ {o = o} .(η↓ _ τ↓) τ↓ (lf↓ _ .τ↓) ϕ↓ ψ↓ = ψ↓ (ηₒ-pos o)
  γ↓ {t = ndₒ o t δₒ εₒ} .(μ↓ σ↓ δ↓) τ↓ (nd↓ σ↓ .τ↓ θ↓ δ↓ ε↓) ϕ↓ ψ↓ =
    let ϕ↓↑ p q = ϕ↓ (μₒ-pos t δₒ p q)
        ψ↓↑ p q = ψ↓ (μₒ-pos t δₒ p q)
        δ↓↑ p = μ↓ (δ↓ p) (ϕ↓↑ p)
        ε↓↑ p = γ↓ (δ↓ p) (Inh↓ σ↓ p) (ε↓ p) (ϕ↓↑ p) (ψ↓↑ p)
    in nd↓ σ↓ τ↓ θ↓ δ↓↑ ε↓↑


