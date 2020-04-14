{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Base
open import Opetopes
open import OpetopicType
open import OpetopicUniverse
open import Sigma
open import HoTT

module PiDep where

  -- Dependent Π

  curry : {Γ : Set} {A : Γ → Set}
    → (B : (γ : Γ) (a : A γ) → Set)
    → Σ Γ A → Set
  curry B (γ , a) = B γ a
  
  Π-cell : {Γ : Set} (A : Γ → Set) (B : (γ : Γ) (a : A γ) → Set)
      → {n : ℕ} {o : 𝕆 n}
      → (f : Frm Γ o) (τ : Cell Γ f)
      → Cell 𝕌 (Frm-𝕌-ap (λ γ → (a : A γ) → B γ a) f)

  postulate

    Π-ap : {Γ : Set} {A : Γ → Set} (B : (γ : Γ) (a : A γ) → Set)
      → {n : ℕ} {o : 𝕆 n} {f : Frm Γ o} (γ : Cell Γ f)
      → Cell-𝕌-ap (λ γ → (a : A γ) → B γ a) γ ↦ Π-cell A B f γ
    {-# REWRITE Π-ap #-}

  rel (Π-cell {Γ} A B (□ γ₀ ▹ γ₁) θ) φ₀ φ₁ = 
      (a₀ : A γ₀) (a₁ : A γ₁)
    → (θ↓ : Cell↓ Γ A (■ a₀ ▸ a₁) θ)
    → Cell↓ (Σ Γ A) (curry B) (■ φ₀ a₀ ▸ φ₁ a₁) (θ , θ↓)
       
  coh (Π-cell {Γ} A B (□ γ₀ ▹ γ₁) θ) φ₀ a₁ =
    let θ↓ = Cell-𝕌-ap A θ
        a₀ = coe θ↓ a₁
        b₀ = φ₀ a₀ 
    in coh (Cell-𝕌-ap (curry B) (θ , coe-rel θ↓ a₁)) b₀

  coe (Π-cell A B (□ γ₀ ▹ γ₁) θ) φ₁ a₀ =
    let θ↓ = Cell-𝕌-ap A θ
        a₁ = coh θ↓ a₀
        b₁ = φ₁ a₁
    in coe (Cell-𝕌-ap (curry B) (θ , coh-rel θ↓ a₀)) b₁
  
  coh-rel (Π-cell A B (□ γ₀ ▹ γ₁) θ) = {!!}
  
  coe-rel (Π-cell A B (□ γ₀ ▹ γ₁) θ) = {!!}
  
  coh-unique (Π-cell A B (□ γ₀ ▹ γ₁) θ) = {!!}
  
  coe-unique (Π-cell A B (□ γ₀ ▹ γ₁) θ) = {!!}
  
  Π-cell A B (f ∥ σ ▹ τ) θ = {!!}

