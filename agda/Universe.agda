{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Base
open import Opetopes
open import OpetopicType
open import OpetopicTypeOver

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


  --
  --  Reflexivity terms are Cell types
  --
  
  Frm↓-𝕌-refl : {A : Set}
    → {n : ℕ} {o : 𝕆 n}
    → Frm↓ 𝕌 (λ X → X) (Frm-refl A o)
    → Frm A o

  Tree↓-𝕌-refl : {A : Set}
    → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → (f↓ : Frm↓ 𝕌 (λ X → X) (Frm-refl A o))
    → (σ↓ : Tree↓ 𝕌 (λ X → X) f↓ (Tree-refl A t))
    → Tree A (Frm↓-𝕌-refl f↓) t
  
  Cell↓-𝕌-refl : {A : Set}
    → {n : ℕ} {o : 𝕆 n} 
    → (f↓ : Frm↓ 𝕌 (λ X → X) (Frm-refl A o))
    → (τ↓ : Cell↓ 𝕌 (λ X → X) f↓ (Cell-refl A o))
    → Cell A (Frm↓-𝕌-refl f↓)
    
  postulate

    Arr-𝕌-refl : {A : Set}
      → Cell-refl {A = 𝕌} A ○ ↦ (λ a₀ a₁ → Cell A (□ a₀ ▹ a₁))
    {-# REWRITE Arr-𝕌-refl #-}

    Cell-𝕌-refl : {A : Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o} 
      → Cell-refl {A = 𝕌} A (o ∣ t) ↦ (λ f↓ σ↓ τ↓ → Cell A (Frm↓-𝕌-refl f↓ ∥ Tree↓-𝕌-refl f↓ σ↓ ▹ Cell↓-𝕌-refl f↓ τ↓))
    {-# REWRITE Cell-𝕌-refl #-}

  Frm↓-𝕌-refl (■ a₀ ▸ a₁) = □ a₀ ▹ a₁
  Frm↓-𝕌-refl (f↓ ∥ σ↓ ▸ τ↓) = Frm↓-𝕌-refl f↓ ∥
    Tree↓-𝕌-refl f↓ σ↓ ▹ Cell↓-𝕌-refl f↓ τ↓
  
  Tree↓-𝕌-refl = {!!}
  
  Cell↓-𝕌-refl (■ a₀ ▸ a₁) p = p
  Cell↓-𝕌-refl (f↓ ∥ σ↓ ▸ τ↓) θ = θ
