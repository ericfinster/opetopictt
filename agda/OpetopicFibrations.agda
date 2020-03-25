{-# OPTIONS --without-K --rewriting #-}

open import Base
open import OpetopicTypes

module OpetopicFibrations where

  data Frm↓ {A : 𝕌} (B : A → 𝕌) : Frm A → 𝕌
  data Tree↓ {A : 𝕌} (B : A → 𝕌) : {f : Frm A} (σ : Tree A f) (f↓ : Frm↓ B f) → 𝕌

  postulate
  
    Cell↓ : {A : 𝕌} (B : A → 𝕌) {f : Frm A} (τ : Cell A f) (f↓ : Frm↓ B f) → 𝕌
    
  data Frm↓ {A : 𝕌} (B : A → 𝕌) where
    ■ : Frm↓ B ●
    _∣_▸_ : {f : Frm A} {σ : Tree A f} {τ : Cell A f}
            (f↓ : Frm↓ B f) (σ↓ : Tree↓ B σ f↓) (τ↓ : Cell↓ B τ f↓)
            → Frm↓ B (f ∥ σ ▸ τ)
    
  data Tree↓ {A : 𝕌} (B : A → 𝕌) where


  postulate

    ∁ell↓Cell : {A : 𝕌} (f : Frm A) (τ : Cell A f) (f↓ : Frm↓ (λ a → Cell A f) f)
      → Cell↓ (λ _ → Cell A f) τ f↓ ↦ {!!}
