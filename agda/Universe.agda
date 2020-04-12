{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Base
open import Opetopes
open import OpetopicType
open import OpetopicTypeOver
open import HoTT

module Universe where

  𝕌 = Set

  postulate

    Arr-𝕌 : {A B : 𝕌} →
      Cell 𝕌 (□ A ▹ B) ↦ (A → B → Set)
    {-# REWRITE Arr-𝕌 #-}

    Cell-𝕌 : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm 𝕌 o} (σ : Tree 𝕌 f t) (τ : Cell 𝕌 f)
      → Cell 𝕌 (f ∥ σ ▹ τ) ↦ ((f↓ : Frm↓ 𝕌 (λ X → X) f) → Tree↓ 𝕌 (λ X → X) f↓ σ → Cell↓ 𝕌 (λ X → X) f↓ τ → Set)
    {-# REWRITE Cell-𝕌 #-}

    Arr↓-𝕌 : {A B : 𝕌} (a : A) (b : B)
      → (R : A → B → Set)
      → Cell↓ 𝕌 (λ X → X) (■ a ▸ b) R ↦ R a b
    {-# REWRITE Arr↓-𝕌 #-}

    Cell↓-𝕌 : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm 𝕌 o} {σ : Tree 𝕌 f t} {τ : Cell 𝕌 f} {θ : Cell 𝕌 (f ∥ σ ▹ τ)}
      → (f↓ : Frm↓ 𝕌 (λ X → X) f) (σ↓ : Tree↓ 𝕌 (λ X → X) f↓ σ) (τ↓ : Cell↓ 𝕌 (λ X → X) f↓ τ)
      → Cell↓ 𝕌 (λ X → X) (f↓ ∥ σ↓ ▸ τ↓) θ ↦ θ f↓ σ↓ τ↓
    {-# REWRITE Cell↓-𝕌 #-}


