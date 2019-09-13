{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Base
open import OpetopicTypes

module Universe where

  init : {A : 𝕌} (f : Frm A)
    → (σ : Tree A f) (τ : Cell A f)
    → A
  init ● (ob α) _ = α
  init (f ∥ σ ▸ τ) _ _ = init f σ τ

  term : {A : 𝕌} (f : Frm A)
    → (σ : Tree A f) (τ : Cell A f)
    → A
  term ● _ τ = τ
  term (f ∥ σ ▸ τ) _ _ = term f σ τ
  
  postulate

    -- Well, okay, equivalences ....
    Univalence : (A B : 𝕌) →
      Cell 𝕌 (● ∥ ob A ▸ B) ↦ A → B

    Frm-𝕌 : (f : Frm 𝕌)
      → (σ₀ : Tree 𝕌 f) (τ₀ : Cell 𝕌 f)
      → (σ₁ : Tree 𝕌 (f ∥ σ₀ ▸ τ₀))
      → (τ₁ : Cell 𝕌 (f ∥ σ₀ ▸ τ₀))
      → init f σ₀ τ₀ → Frm (term f σ₀ τ₀)
      
    Cell-𝕌 : (f : Frm 𝕌)
      → (σ₀ : Tree 𝕌 f) (τ₀ : Cell 𝕌 f)
      → (σ₁ : Tree 𝕌 (f ∥ σ₀ ▸ τ₀))
      → (τ₁ : Cell 𝕌 (f ∥ σ₀ ▸ τ₀))
      → (i : init f σ₀ τ₀)
      → Cell 𝕌 (f ∥ σ₀ ▸ τ₀ ∥ σ₁ ▸ τ₁) ↦ Cell (term f σ₀ τ₀) (Frm-𝕌 f σ₀ τ₀ σ₁ τ₁ i)

  
