{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Base
open import Opetopes
open import OpetopicType
open import HoTT

module Universe where

  𝕌 = Set

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
  --  The canonical fibration
  --

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

  Tree-el-typ : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → {f : Frm 𝕌 o} (f↓ : Frm-el f)
    → {σ : Tree 𝕌 f t} (σ↓ : Tree-el f↓ σ)
    → (p : Pos t)
    → Frm-el (Typ σ p)

  Tree-el-inh : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → {f : Frm 𝕌 o} (f↓ : Frm-el f)
    → {σ : Tree 𝕌 f t} (σ↓ : Tree-el f↓ σ)
    → (p : Pos t)
    → Cell-el (Tree-el-typ f↓ σ↓ p) (Inh σ p)

  Tree-el-η : {n : ℕ} {o : 𝕆 n} 
    → {f : Frm 𝕌 o} (f↓ : Frm-el f)
    → (τ : Cell 𝕌 f)
    → Tree-el f↓ (η f τ)
    → Cell-el f↓ τ

  Tree-el-μ : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
    → {f : Frm 𝕌 o} (f↓ : Frm-el f)
    → (σ : Tree 𝕌 f t) (σ↓ : Tree-el f↓ σ)
    → (δ : (p : Pos t) → Tree 𝕌 (Typ σ p) (δₒ p))
    → (ρ : Tree-el f↓ (μ σ δ))
    → (p : Pos t) → Tree-el (Tree-el-typ f↓ σ↓ p) (δ p)

  postulate

    Arr-𝕌 : {A B : 𝕌} →
      Cell 𝕌 (□ A ▹ B) ↦ A ≃ B 
    {-# REWRITE Arr-𝕌 #-}

    Cell-𝕌 : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm 𝕌 o} (σ : Tree 𝕌 f t) (τ : Cell 𝕌 f)
      → Cell 𝕌 (f ∥ σ ▹ τ) ↦ ((f↓ : Frm-el f) → Tree-el f↓ σ ≃ Cell-el f↓ τ)
    {-# REWRITE Cell-𝕌 #-}

  Frm-el (□ A ▹ B) = A × B
  Frm-el (f ∥ σ ▹ τ) = Σ (Frm-el f) (λ f↓ → Tree-el f↓ σ × Cell-el f↓ τ)
  
  Tree-el (a₀ , a₁) (nil A) = Cell A (□ a₀ ▹ a₁) 
  Tree-el (a , c) (cns {a₀ = A} {a₁ = B} {a₂ = C} ρ σ) = Σ B (λ b → rel ρ b c × Tree-el (a , b) σ) 
  Tree-el (f↓ , σ↓ , τ↓) (lf f τ) = Cell (Cell-el f↓ τ) (□ Tree-el-η f↓ τ σ↓ ▹ τ↓)
  Tree-el {t = ndₒ o t δₒ εₒ} (f↓ , ρ↓ , τ↓) (nd σ τ θ δ ε) =
    Σ (Tree-el f↓ σ) (λ σ↓ →
    Σ (rel (θ f↓) σ↓ τ↓) (λ θ↓ →
    (p : Pos t) → Tree-el (Tree-el-typ f↓ σ↓ p , Tree-el-μ f↓ σ σ↓ δ ρ↓ p  , Tree-el-inh f↓ σ↓ p) (ε p)))
  
  Cell-el {f = □ A ▹ B} (a , b) E = rel E a b
  Cell-el {f = f ∥ σ ▹ τ} (f↓ , σ↓ , τ↓) E = rel (E f↓) σ↓ τ↓

  Tree-el-typ (a , c) {σ = cns ρ σ} (b , ρ↓ , σ↓) (inl unit) = b , c
  Tree-el-typ (a , c) {σ = cns ρ σ} (b , ρ↓ , σ↓) (inr p) = Tree-el-typ (a , b) σ↓ p
  Tree-el-typ (f↓ , ρ↓ , τ↓) {σ = nd σ τ θ δ ε} (σ↓ , θ↓ , ε↓) (inl unit) = f↓ , σ↓ , τ↓
  Tree-el-typ (f↓ , ρ↓ , τ↓) {σ = nd σ τ θ δ ε} (σ↓ , θ↓ , ε↓) (inr (p , q)) = Tree-el-typ _ (ε↓ p) q
  
  Tree-el-inh (a , c) {σ = cns ρ σ} (b , ρ↓ , σ↓) (inl unit) = ρ↓
  Tree-el-inh (a , c) {σ = cns ρ σ} (b , ρ↓ , σ↓) (inr p) = Tree-el-inh (a , b) σ↓ p
  Tree-el-inh (f↓ , ρ↓ , τ↓) {σ = nd σ τ θ δ ε} (σ↓ , θ↓ , ε↓) (inl unit) = θ↓
  Tree-el-inh (f↓ , ρ↓ , τ↓) {σ = nd σ τ θ δ ε} (σ↓ , θ↓ , ε↓) (inr (p , q)) = Tree-el-inh _ (ε↓ p) q

  -- Tree-el-η : {n : ℕ} {o : 𝕆 n} 
  --   → {f : Frm 𝕌 o} (f↓ : Frm-el f)
  --   → (τ : Cell 𝕌 f)
  --   → Tree-el f↓ (η f τ)
  --   → Cell-el f↓ τ
  Tree-el-η {f = □ A ▹ B} (a₀ , b) τ (a₁ , τ↓ , p) = coe (Cell-𝕌-ap (λ a → rel τ a b) p) τ↓
  Tree-el-η {f = f ∥ σ ▹ τ} (f↓ , σ↓ , τ↓) E (σ↓' , θ↓ , ε↓) = {!!}
  -- Appears I need to prove that σ↓ == σ↓'.  But how?

  Tree-el-μ = {!!}

  --
  --  Cells over using primitive ap
  --
  
  Frm↓ : (A : Set) (B : A → Set)
    → {n : ℕ} {o : 𝕆 n}
    → (f : Frm A o) → Set
  Frm↓ A B f = Frm-el (Frm-𝕌-ap B f)
  
  Tree↓ : (A : Set) (B : A → Set) 
      {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → {f : Frm A o} (f↓ : Frm↓ A B f)
    → (σ : Tree A f t) → Set
  Tree↓ A B f↓ σ = Tree-el f↓ (Tree-𝕌-ap B σ) 

  Cell↓ : (A : Set) (B : A → Set)
    → {n : ℕ} {o : 𝕆 n} {f : Frm A o}
    → (f↓ : Frm↓ A B f) (τ : Cell A f)
    → Set
  Cell↓ A B f↓ τ = Cell-el f↓ (Cell-𝕌-ap B τ)

  --
  --  The equations for Π now seem to work ...
  --

  Π-cell : {Γ : Set} (A : Γ → Set) (B : (γ : Γ) (a : A γ) → Set)
      → {n : ℕ} {o : 𝕆 n}
      → (f : Frm Γ o) (τ : Cell Γ f)
      → Cell 𝕌 (Frm-𝕌-ap (λ γ → (a : A γ) → B γ a) f)

  postulate

    Π-ap : {Γ : Set} {A : Γ → Set} (B : (γ : Γ) (a : A γ) → Set)
      → {n : ℕ} {o : 𝕆 n} {f : Frm Γ o} (γ : Cell Γ f)
      → Cell-𝕌-ap (λ γ → (a : A γ) → B γ a) γ ↦ Π-cell A B f γ
    {-# REWRITE Π-ap #-}

  rel (Π-cell A B (□ γ₀ ▹ γ₁) θ) φ₀ φ₁ = {!!}
  coh (Π-cell A B (□ γ₀ ▹ γ₁) θ) = {!!}
  coe (Π-cell A B (□ γ₀ ▹ γ₁) θ) = {!!}
  coh-rel (Π-cell A B (□ γ₀ ▹ γ₁) θ) = {!!}
  coe-rel (Π-cell A B (□ γ₀ ▹ γ₁) θ) = {!!}
  coh-unique (Π-cell A B (□ γ₀ ▹ γ₁) θ) = {!!}
  coe-unique (Π-cell A B (□ γ₀ ▹ γ₁) θ) = {!!}
  Π-cell A B (f ∥ σ ▹ τ) θ = {!!}
