{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Base
open import Opetopes
open import OpetopicType

module Universe where

  𝕌 = Set
  
  Frm-el : {n : ℕ} {o : 𝕆 n}
    → Frm 𝕌 o → Set

  Tree-el : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → {f : Frm 𝕌 o} (f↓ : Frm-el f)
    → (σ : Tree 𝕌 f t)
    → Set

  Cell-el : {n : ℕ} {o : 𝕆 n} 
    → {f : Frm 𝕌 o} (f↓ : Frm-el f)
    → (τ : Cell 𝕌 f)
    → Set

  postulate

    Arr-𝕌 : {A B : 𝕌} →
      Cell 𝕌 (□ A ▹ B) ↦ (A → B → Set)
    {-# REWRITE Arr-𝕌 #-}

    Cell-𝕌 : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm 𝕌 o} (σ : Tree 𝕌 f t) (τ : Cell 𝕌 f)
      → Cell 𝕌 (f ∥ σ ▹ τ) ↦ ((f↓ : Frm-el f) → Tree-el f↓ σ → Cell-el f↓ τ → Set)
    {-# REWRITE Cell-𝕌 #-}

  Frm-el (□ A ▹ B) = A × B
  Frm-el (f ∥ σ ▹ τ) = Σ (Frm-el f) (λ f↓ → Tree-el f↓ σ × Cell-el f↓ τ)
  
  Tree-el (a₀ , a₁) (nil A) = Cell A (□ a₀ ▹ a₁) 
  Tree-el (a , c) (cns {a₀ = A} {a₁ = B} {a₂ = C} ρ σ) = Σ B (λ b → ρ b c × Tree-el (a , b) σ)
  Tree-el (f↓ , σ↓ , τ↓) (lf f τ) = {!!}
  -- 
  Tree-el (f↓ , σ↓ , τ↓) (nd σ τ θ δ ε) = {!!}

  Cell-el {f = □ A ▹ B} (a , b) E = E a b
  Cell-el {f = f ∥ σ ▹ τ} (f↓ , σ↓ , τ↓) E = E f↓ σ↓ τ↓


  -- Ap into the universe

  Frm-𝕌-ap : {A : Set} (B : A → Set)
      → {n : ℕ} {o : 𝕆 n}
      → Frm A o → Frm 𝕌 o

  Tree-𝕌-ap : {A : Set} (B : A → Set)
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm A o} (σ : Tree A f t)
      → Tree 𝕌 (Frm-𝕌-ap B f) t
      
  postulate

    Cell-𝕌-ap : {A : Set} (B : A → Set)
      → {n : ℕ} {o : 𝕆 n} {f : Frm A o}
      → Cell A f → Cell 𝕌 (Frm-𝕌-ap B f)

    Tree-𝕌-ap-typ : {A : Set} (B : A → Set)
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → (f : Frm A o) (σ : Tree A f t)
      → (p : Pos t)
      → Typ (Tree-𝕌-ap B σ) p ↦ Frm-𝕌-ap B (Typ σ p)
    {-# REWRITE Tree-𝕌-ap-typ #-}

    Tree-𝕌-ap-inh : {A : Set} (B : A → Set)
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → (f : Frm A o) (σ : Tree A f t)
      → (p : Pos t)
      → Inh (Tree-𝕌-ap B σ) p ↦ Cell-𝕌-ap B (Inh σ p)
    {-# REWRITE Tree-𝕌-ap-inh #-}

    Tree-𝕌-ap-η : {A : Set} (B : A → Set)
      → {n : ℕ} {o : 𝕆 n} 
      → (f : Frm A o) (τ : Cell A f)
      → Tree-𝕌-ap B (η f τ) ↦ η (Frm-𝕌-ap B f) (Cell-𝕌-ap B τ)
    {-# REWRITE Tree-𝕌-ap-η #-}

    Tree-𝕌-ap-μ : {A : Set} (B : A → Set)
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
      → {f : Frm A o} (σ : Tree A f t)
      → (δ : (p : Pos t) → Tree A (Typ σ p) (δₒ p))
      → Tree-𝕌-ap B (μ σ δ) ↦ μ (Tree-𝕌-ap B σ) (λ p → Tree-𝕌-ap B (δ p))
    {-# REWRITE Tree-𝕌-ap-μ #-}

  Frm-𝕌-ap B (□ a₀ ▹ a₁) = □ B a₀ ▹ B a₁
  Frm-𝕌-ap B (f ∥ σ ▹ τ) = Frm-𝕌-ap B f ∥ Tree-𝕌-ap B σ ▹ Cell-𝕌-ap B τ
  
  Tree-𝕌-ap B (nil a) = nil (B a)
  Tree-𝕌-ap B (cns ρ σ) = cns (Cell-𝕌-ap B ρ) (Tree-𝕌-ap B σ)
  Tree-𝕌-ap B (lf f τ) = lf (Frm-𝕌-ap B f) (Cell-𝕌-ap B τ)
  Tree-𝕌-ap B (nd σ τ θ δ ε) =
    nd (Tree-𝕌-ap B σ) (Cell-𝕌-ap B τ) (Cell-𝕌-ap B θ)
       (λ p → Tree-𝕌-ap B (δ p))
       (λ p → Tree-𝕌-ap B (ε p))

  --
  --  A recursive definition of cells over
  --
  
  -- Frm↓ : (A : Set) (B : A → Set)
  --   → {n : ℕ} {o : 𝕆 n}
  --   → (f : Frm A o) → Set

  -- Tree↓ : (A : Set) (B : A → Set) 
  --     {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
  --   → {f : Frm A o} (f↓ : Frm↓ A B f)
  --   → (σ : Tree A f t) → Set

  -- Cell↓ : (A : Set) (B : A → Set)
  --   → {n : ℕ} {o : 𝕆 n} {f : Frm A o}
  --   → (f↓ : Frm↓ A B f) (τ : Cell A f)
  --   → Set

  -- Frm↓ A B (□ a₀ ▹ a₁) = B a₀ × B a₁
  -- Frm↓ A B (f ∥ σ ▹ τ) = Σ (Frm↓ A B f) (λ f↓ → Tree↓ A B f↓ σ × Cell↓ A B f↓ τ )
  
  -- Tree↓ A B f↓ σ = {!(Tree-𝕌-ap B σ)!}
  
  -- Cell↓ A B {f = □ a₀ ▹ a₁} (b₀ , b₁) τ = Cell-𝕌-ap B τ b₀ b₁
  -- Cell↓ A B {f = f ∥ σ ▹ τ} (f↓ , σ↓ , τ↓) θ = {!Cell-𝕌-ap B θ !}

  -- Π-𝕌-ap : {Γ : Set} {A : Γ → Set} {B : (γ : Γ) (a : A γ) → Set}
  --   → {n : ℕ} {o : 𝕆 n} {f : Frm Γ o} (γ : Cell Γ f)
  --   → Cell-𝕌-ap (λ γ → (a : A γ) → B γ a) γ ↦ {!!}
