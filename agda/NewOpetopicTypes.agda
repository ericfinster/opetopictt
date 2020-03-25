{-# OPTIONS --without-K --rewriting #-}

open import Base

module NewOpetopicTypes where

  data Frm (A : 𝕌) : A → A → 𝕌
  data Tree (A : 𝕌) : {a₀ a₁ : A} (f : Frm A a₀ a₁) → 𝕌

  postulate

    Cell : (A : 𝕌) {a₀ a₁ : A} (f : Frm A a₀ a₁) → 𝕌
    
    Pos : {A : 𝕌} {a₀ a₁ : A} (f : Frm A a₀ a₁)
      → Tree A f → A → A → 𝕌

    Typ : {A : 𝕌} {a₀ a₁ : A} (f : Frm A a₀ a₁)
      → (σ : Tree A f) {a₂ a₃ : A} (p : Pos f σ a₂ a₃) → Frm A a₂ a₃
    
    Inh : {A : 𝕌} {a₀ a₁ : A} (f : Frm A a₀ a₁)
      → (σ : Tree A f) {a₂ a₃ : A} (p : Pos f σ a₂ a₃) → Cell A (Typ f σ p)

    η : {A : 𝕌} {a₀ a₁ : A} (f : Frm A a₀ a₁)
      → Cell A f → Tree A f

    μ : {A : 𝕌} {a₀ a₁ : A} (f : Frm A a₀ a₁)
      → (σ : Tree A f)
      → (κ : {a₂ a₃ : A} (p : Pos f σ a₂ a₃) → Tree A (Typ f σ p))
      → Tree A f
  
  data Frm (A : 𝕌) where
    ●_▸_ : (a₀ : A) (a₁ : A) → Frm A a₀ a₁
    _∣_▸_ : {a₀ a₁ : A} (f : Frm A a₀ a₁)
      → (σ : Tree A f) (τ : Cell A f)
      → Frm A a₀ a₁

  data Tree (A : 𝕌) where

    -- Somewhat strange that dim 1 gets singled out here.
    -- But I'm not sure if I see any way around it if you
    -- would like the frames, cells, and trees to depend
    -- of A, which clearly seems like a desiderata ....
    
    lf₁ : (a₀ : A) → Tree A (● a₀ ▸ a₀)
    nd₁ : (a₀ a₁ a₂ : A) → Cell A (● a₀ ▸ a₁)
      → Tree A (● a₁ ▸ a₂) → Tree A (● a₀ ▸ a₂)

    lf : {a₀ a₁ : A} (f : Frm A a₀ a₁) (τ : Cell A f)
      → Tree A (f ∣ η f τ ▸ τ)
    nd : {a₀ a₁ : A} (f : Frm A a₀ a₁)
      → (σ : Tree A f) (τ : Cell A f)  (α : Cell A (f ∣ σ ▸ τ))
      → (δ : {a₂ a₃ : A} (p : Pos f σ a₂ a₃) → Tree A (Typ f σ p))
      → (ε : {a₂ a₃ : A} (p : Pos f σ a₂ a₃) → Tree A (Typ f σ p ∣ δ p ▸ Inh f σ p))
      → Tree A (f ∣ μ f σ δ ▸ τ)
