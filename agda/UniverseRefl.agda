{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Base
open import Opetopes
open import OpetopicType
open import OpetopicTypeOver
open import Universe

module UniverseRefl where

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

    Tree↓-𝕌-refl-typ : {A : Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → (f↓ : Frm↓ 𝕌 (λ X → X) (Frm-refl A o))
      → (σ↓ : Tree↓ 𝕌 (λ X → X) f↓ (Tree-refl A t))
      → (p : Pos t)
      → Typ (Tree↓-𝕌-refl f↓ σ↓) p ↦ Frm↓-𝕌-refl (Typ↓ σ↓ p)
    {-# REWRITE Tree↓-𝕌-refl-typ #-}

    Tree↓-𝕌-refl-inh : {A : Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → (f↓ : Frm↓ 𝕌 (λ X → X) (Frm-refl A o))
      → (σ↓ : Tree↓ 𝕌 (λ X → X) f↓ (Tree-refl A t))
      → (p : Pos t)
      → Inh (Tree↓-𝕌-refl f↓ σ↓) p ↦ Cell↓-𝕌-refl (Typ↓ σ↓ p) (Inh↓ σ↓ p)
    {-# REWRITE Tree↓-𝕌-refl-inh #-}

    Tree↓-𝕌-refl-η : {A : Set}
      → {n : ℕ} {o : 𝕆 n} 
      → (f↓ : Frm↓ 𝕌 (λ X → X) (Frm-refl A o))
      → (τ↓ : Cell↓ 𝕌 (λ X → X) f↓ (Cell-refl A o))
      → Tree↓-𝕌-refl f↓ (η↓ f↓ τ↓) ↦ η (Frm↓-𝕌-refl f↓) (Cell↓-𝕌-refl f↓ τ↓)
    {-# REWRITE Tree↓-𝕌-refl-η #-}

    Tree↓-𝕌-refl-μ : {A : Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
      → (f↓ : Frm↓ 𝕌 (λ X → X) (Frm-refl A o))
      → (σ↓ : Tree↓ 𝕌 (λ X → X) f↓ (Tree-refl A t))
      → (δ↓ : (p : Pos t) → Tree↓ 𝕌 (λ X → X) (Typ↓ σ↓ p) (Tree-refl A (δₒ p)))
      → Tree↓-𝕌-refl f↓ (μ↓ σ↓ δ↓) ↦ μ (Tree↓-𝕌-refl f↓ σ↓) (λ p → Tree↓-𝕌-refl (Typ↓ σ↓ p) (δ↓ p))
    {-# REWRITE Tree↓-𝕌-refl-μ #-}
    
  Frm↓-𝕌-refl (■ a₀ ▸ a₁) = □ a₀ ▹ a₁
  Frm↓-𝕌-refl (f↓ ∥ σ↓ ▸ τ↓) = Frm↓-𝕌-refl f↓ ∥
    Tree↓-𝕌-refl f↓ σ↓ ▹ Cell↓-𝕌-refl f↓ τ↓
  
  Tree↓-𝕌-refl ._ (nil↓ a) = nil a
  Tree↓-𝕌-refl ._ (cns↓ ρ↓ σ↓) = cns ρ↓ (Tree↓-𝕌-refl _ σ↓)
  Tree↓-𝕌-refl ._ (lf↓ f↓ τ↓) = lf (Frm↓-𝕌-refl f↓) (Cell↓-𝕌-refl f↓ τ↓)
  Tree↓-𝕌-refl ._ (nd↓ {f↓ = f↓} σ↓ τ↓ θ↓ δ↓ ε↓) =
    nd (Tree↓-𝕌-refl f↓ σ↓) (Cell↓-𝕌-refl f↓ τ↓) (Cell↓-𝕌-refl (f↓ ∥ σ↓ ▸ τ↓) θ↓)
       (λ p → Tree↓-𝕌-refl (Typ↓ σ↓ p) (δ↓ p))
       (λ p → Tree↓-𝕌-refl _ (ε↓ p))
  
  Cell↓-𝕌-refl (■ a₀ ▸ a₁) p = p
  Cell↓-𝕌-refl (f↓ ∥ σ↓ ▸ τ↓) θ = θ
