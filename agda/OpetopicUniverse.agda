{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Base
open import Opetopes
open import OpetopicType
open import HoTT

module OpetopicUniverse where

  𝕌 = Set

  data Frm-el : {n : ℕ} {o : 𝕆 n} → Frm 𝕌 o → Set
  data Tree-el : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → {f : Frm 𝕌 o} (f↓ : Frm-el f)
    → (σ : Tree 𝕌 f t)
    → Set

  postulate
  
    Cell-el : {n : ℕ} {o : 𝕆 n} 
      → {f : Frm 𝕌 o} (f↓ : Frm-el f)
      → (τ : Cell 𝕌 f)
      → Set

  Typ-el : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → {f : Frm 𝕌 o} {σ : Tree 𝕌 f t}
    → {f↓ : Frm-el f} (σ↓ : Tree-el f↓ σ)
    → (p : Pos t)
    → Frm-el (Typ σ p)
  
  Inh-el : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → {f : Frm 𝕌 o} {σ : Tree 𝕌 f t}
    → {f↓ : Frm-el f} (σ↓ : Tree-el f↓ σ)
    → (p : Pos t)
    → Cell-el (Typ-el σ↓ p) (Inh σ p)
  
  infixl 30 _∥_▸_

  data Frm-el where
    ■_▸_ : {A B : 𝕌}
      → (a : A) (b : B)
      → Frm-el (□ A ▹ B)
    _∥_▸_ : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm 𝕌 o} (f↓ : Frm-el f)
      → {σ : Tree 𝕌 f t} (σ↓ : Tree-el f↓ σ)
      → {τ : Cell 𝕌 f} (τ↓ : Cell-el f↓ τ)
      → Frm-el (f ∥ σ ▹ τ)

  η-el : {n : ℕ} {o : 𝕆 n}
    → {f : Frm 𝕌 o} {τ : Cell 𝕌 f}
    → (f↓ : Frm-el f) (τ↓ : Cell-el f↓ τ)
    → Tree-el f↓ (η f τ)

  μ-el : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
    → {f : Frm 𝕌 o} {σ : Tree 𝕌 f t}
    → {δ : (p : Pos t) → Tree 𝕌 (Typ σ p) (δₒ p)}
    → {f↓ : Frm-el f} (σ↓ : Tree-el f↓ σ)
    → (δ↓ : (p : Pos t) → Tree-el (Typ-el σ↓ p) (δ p))
    → Tree-el f↓ (μ σ δ)
    
  α-el : {t₀ : 𝕋 ○} {t₁ : 𝕋 ○}
    → {A : 𝕌} {B : 𝕌} {C : 𝕌} 
    → {σ₀ : Tree 𝕌 (□ B ▹ C) t₀} {σ₁ : Tree 𝕌 (□ A ▹ B) t₁}
    → {a : A} {b : B} {c : C}
    → (σ↓₀ : Tree-el (■ b ▸ c) σ₀)
    → (σ↓₁ : Tree-el (■ a ▸ b) σ₁)
    → Tree-el (■ a ▸ c) (α σ₀ σ₁)
  
  γ-el : {n : ℕ} {o : 𝕆 n} {s : 𝕋 o} {t : 𝕋 (o ∣ s)}
    → {ϕₒ : (p : Pos s) → 𝕋 (Typₒ s p)}
    → {ψₒ : (p : Pos s) → 𝕋 (Typₒ s p ∣ ϕₒ p)}
    → {f : Frm 𝕌 o} {σ : Tree 𝕌 f s}
    → {τ : Cell 𝕌 f} {ρ : Tree 𝕌 (f ∥ σ ▹ τ) t}
    → {ϕ : (p : Pos s) → Tree 𝕌 (Typ σ p) (ϕₒ p)}
    → {ψ : (p : Pos s) → Tree 𝕌 (Typ σ p ∥ ϕ p ▹ Inh σ p) (ψₒ p)}
    → {f↓ : Frm-el f} (σ↓ : Tree-el f↓ σ)
    → (τ↓ : Cell-el f↓ τ) (ρ↓ : Tree-el (f↓ ∥ σ↓ ▸ τ↓) ρ)
    → (ϕ↓ : (p : Pos s) → Tree-el (Typ-el σ↓ p) (ϕ p))
    → (ψ↓ : (p : Pos s) → Tree-el (Typ-el σ↓ p ∥ ϕ↓ p ▸ Inh-el σ↓ p) (ψ p))
    → Tree-el (f↓ ∥ μ-el σ↓ ϕ↓ ▸ τ↓) (γ σ τ ρ ϕ ψ)

  data Tree-el where

    nil-el : {A : Set} (a : A)
      → Tree-el (■ a ▸ a) (nil A)

    cns-el : {t : 𝕋 ○} {A B C : Set}
      → {ρ : Cell 𝕌 (□ B ▹ C)} {σ : Tree 𝕌 (□ A ▹ B) t}
      → {a : A} {b : B} {c : C}
      → (ρ↓ : Cell-el (■ b ▸ c) ρ) (σ↓ : Tree-el (■ a ▸ b) σ)
      → Tree-el (■ a ▸ c) (cns ρ σ)

    lf-el : {n : ℕ} {o : 𝕆 n}
      → {f : Frm 𝕌 o} {τ : Cell 𝕌 f}
      → (f↓ : Frm-el f) (τ↓ : Cell-el f↓ τ)
      → Tree-el (f↓ ∥ η-el f↓ τ↓ ▸ τ↓) (lf f τ)

    nd-el : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
      → {εₒ : (p : Pos t) → 𝕋 (Typₒ t p ∣ δₒ p)}
      → {f : Frm 𝕌 o} {σ : Tree 𝕌 f t} {τ : Cell 𝕌 f}
      → {θ : Cell 𝕌 (f ∥ σ ▹ τ)}
      → {δ : (p : Pos t) → Tree 𝕌 (Typ σ p) (δₒ p)}
      → {ε : (p : Pos t) → Tree 𝕌 (Typ σ p ∥ δ p ▹ Inh σ p) (εₒ p)}
      → {f↓ : Frm-el f} (σ↓ : Tree-el f↓ σ) (τ↓ : Cell-el f↓ τ)
      → (θ↓ : Cell-el (f↓ ∥ σ↓ ▸ τ↓) θ)
      → (δ↓ : (p : Pos t) → Tree-el (Typ-el σ↓ p) (δ p))
      → (ε↓ : (p : Pos t) → Tree-el (Typ-el σ↓ p ∥ δ↓ p ▸ Inh-el σ↓ p) (ε p))
      → Tree-el (f↓ ∥ μ-el σ↓ δ↓ ▸ τ↓) (nd σ τ θ δ ε)

  Typ-el (cns-el {b = b} {c = c} ρ↓ σ↓) (inl unit) = ■ b ▸ c
  Typ-el (cns-el ρ↓ σ↓) (inr p) = Typ-el σ↓ p
  Typ-el (nd-el {f↓ = f↓} σ↓ τ↓ θ↓ δ↓ ε↓) (inl unit) = f↓ ∥ σ↓ ▸ τ↓ 
  Typ-el (nd-el σ↓ τ↓ θ↓ δ↓ ε↓) (inr (p , q)) = Typ-el (ε↓ p) q
  
  Inh-el (cns-el ρ↓ σ↓) (inl unit) = ρ↓
  Inh-el (cns-el ρ↓ σ↓) (inr p) = Inh-el σ↓ p
  Inh-el (nd-el σ↓ τ↓ θ↓ δ↓ ε↓) (inl unit) = θ↓ 
  Inh-el (nd-el σ↓ τ↓ θ↓ δ↓ ε↓) (inr (p , q)) = Inh-el (ε↓ p) q

  postulate

    -- Typ/Inh laws
    
    η-el-pos-typ : {n : ℕ} {o : 𝕆 n}
      → {f : Frm 𝕌 o} {τ : Cell 𝕌 f}
      → (f↓ : Frm-el f) (τ↓ : Cell-el f↓ τ)
      → (p : Pos (ηₒ o))
      → Typ-el (η-el f↓ τ↓) p ↦ f↓
    {-# REWRITE η-el-pos-typ #-}

    η-el-pos-inh : {n : ℕ} {o : 𝕆 n}
      → {f : Frm 𝕌 o} {τ : Cell 𝕌 f}
      → (f↓ : Frm-el f) (τ↓ : Cell-el f↓ τ)
      → (p : Pos (ηₒ o))
      → Inh-el (η-el f↓ τ↓) p ↦ τ↓
    {-# REWRITE η-el-pos-inh #-}

    μ-el-pos-typ : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
      → {f : Frm 𝕌 o} {σ : Tree 𝕌 f t}
      → {δ : (p : Pos t) → Tree 𝕌 (Typ σ p) (δₒ p)}
      → {f↓ : Frm-el f} (σ↓ : Tree-el f↓ σ)
      → (δ↓ : (p : Pos t) → Tree-el (Typ-el σ↓ p) (δ p))
      → (p : Pos (μₒ t δₒ))
      → Typ-el (μ-el σ↓ δ↓) p ↦ Typ-el (δ↓ (μₒ-pos-fst t δₒ p)) (μₒ-pos-snd t δₒ p)
    {-# REWRITE μ-el-pos-typ #-}
    
    μ-el-pos-inh : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
      → {f : Frm 𝕌 o} {σ : Tree 𝕌 f t}
      → {δ : (p : Pos t) → Tree 𝕌 (Typ σ p) (δₒ p)}
      → {f↓ : Frm-el f} (σ↓ : Tree-el f↓ σ)
      → (δ↓ : (p : Pos t) → Tree-el (Typ-el σ↓ p) (δ p))
      → (p : Pos (μₒ t δₒ))
      → Inh-el (μ-el σ↓ δ↓) p ↦ Inh-el (δ↓ (μₒ-pos-fst t δₒ p)) (μₒ-pos-snd t δₒ p)
    {-# REWRITE μ-el-pos-inh #-}
    
    -- μ-el laws
    μ-el-unit-r : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm 𝕌 o} {σ : Tree 𝕌 f t}
      → (f↓ : Frm-el f) (σ↓ : Tree-el f↓ σ)
      → μ-el σ↓ (λ p → η-el (Typ-el σ↓ p) (Inh-el σ↓ p)) ↦ σ↓
    {-# REWRITE μ-el-unit-r #-}

    μ-el-unit-l : {n : ℕ} {o : 𝕆 n}
      → (δₒ : (p : Pos (ηₒ o)) → 𝕋 o)      
      → {f : Frm 𝕌 o} {τ : Cell 𝕌 f}
      → {δ : (p : Pos (ηₒ o)) → Tree 𝕌 (Typ (η f τ) p) (δₒ p)}
      → (f↓ : Frm-el f) (τ↓ : Cell-el f↓ τ)
      → (δ↓ : (p : Pos (ηₒ o)) → Tree-el (Typ-el (η-el f↓ τ↓) p) (δ p))
      → μ-el (η-el f↓ τ↓) δ↓ ↦ δ↓ (ηₒ-pos o)
    {-# REWRITE μ-el-unit-l #-}
    
    μ-el-assoc : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → (δₒ : (p : Pos t) → 𝕋 (Typₒ t p))
      → (εₒ : (p : Pos (μₒ t δₒ)) → 𝕋 (Typₒ (μₒ t δₒ) p))
      → {f : Frm 𝕌 o} {σ : Tree 𝕌 f t}
      → {δ : (p : Pos t) → Tree 𝕌 (Typ σ p) (δₒ p)}
      → {ε : (p : Pos (μₒ t δₒ)) → Tree 𝕌 (Typ (μ σ δ) p) (εₒ p)}
      → (f↓ : Frm-el f) (σ↓ : Tree-el f↓ σ)
      → (δ↓ : (p : Pos t) → Tree-el (Typ-el σ↓ p) (δ p))
      → (ε↓ : (p : Pos (μₒ t δₒ)) → Tree-el (Typ-el (μ-el σ↓ δ↓) p) (ε p))
      → μ-el (μ-el σ↓ δ↓) ε↓ ↦ μ-el σ↓ (λ p → μ-el (δ↓ p) (λ q →  ε↓ (μₒ-pos t δₒ p q)))
    {-# REWRITE μ-el-assoc #-}


  η-el (■ b₀ ▸ b₁) τ↓ = cns-el τ↓ (nil-el b₀) 
  η-el (f↓ ∥ σ↓ ▸ τ↓) θ↓ = 
    let η-el-dec p = η-el (Typ-el σ↓ p) (Inh-el σ↓ p)
        lf-el-dec p = lf-el (Typ-el σ↓ p) (Inh-el σ↓ p)
    in nd-el σ↓ τ↓ θ↓ η-el-dec lf-el-dec 

  μ-el (nil-el b) κ↓ = nil-el b
  μ-el (cns-el ρ↓ σ↓) κ↓ =
    let w↓ = κ↓ (inl unit)
        κ↓↑ p = κ↓ (inr p)
    in α-el w↓ (μ-el σ↓ κ↓↑)
  μ-el (lf-el f↓ τ↓) κ↓ = lf-el f↓ τ↓
  μ-el (nd-el σ↓ τ↓ θ↓ δ↓ ε↓) κ↓ =
    let w↓ = κ↓ (inl unit)
        κ↓↑ p q = κ↓ (inr (p , q))
        ψ↓ p = μ-el (ε↓ p) (κ↓↑ p)
    in γ-el σ↓ τ↓ w↓ δ↓ ψ↓

  α-el (nil-el _) σ↓₁ = σ↓₁
  α-el (cns-el ρ↓ σ↓₀) σ↓₁ = cns-el ρ↓ (α-el σ↓₀ σ↓₁)

  γ-el {o = o} .(η-el _ τ↓) τ↓ (lf-el _ .τ↓) ϕ↓ ψ↓ = ψ↓ (ηₒ-pos o)
  γ-el {t = ndₒ o t δₒ εₒ} .(μ-el σ↓ δ↓) τ↓ (nd-el σ↓ .τ↓ θ↓ δ↓ ε↓) ϕ↓ ψ↓ =
    let ϕ↓↑ p q = ϕ↓ (μₒ-pos t δₒ p q)
        ψ↓↑ p q = ψ↓ (μₒ-pos t δₒ p q)
        δ↓↑ p = μ-el (δ↓ p) (ϕ↓↑ p)
        ε↓↑ p = γ-el (δ↓ p) (Inh-el σ↓ p) (ε↓ p) (ϕ↓↑ p) (ψ↓↑ p)
    in nd-el σ↓ τ↓ θ↓ δ↓↑ ε↓↑

  postulate

    Arr-𝕌 : {A B : 𝕌} →
      Cell 𝕌 (□ A ▹ B) ↦ A ≃ B 
    {-# REWRITE Arr-𝕌 #-}

    Cell-𝕌 : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm 𝕌 o} (σ : Tree 𝕌 f t) (τ : Cell 𝕌 f)
      → Cell 𝕌 (f ∥ σ ▹ τ) ↦ ((f↓ : Frm-el f) → Tree-el f↓ σ ≃ Cell-el f↓ τ)
    {-# REWRITE Cell-𝕌 #-}

    Arr-𝕌↓ : {A B : 𝕌}
      → (a : A) (b : B) (E : A ≃ B)
      → Cell-el (■ a ▸ b) E ↦ rel E a b
    {-# REWRITE Arr-𝕌↓ #-}

    Cell-𝕌↓ : {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm 𝕌 o} (σ : Tree 𝕌 f t) (τ : Cell 𝕌 f)
      → {f↓ : Frm-el f} (σ↓ : Tree-el f↓ σ) (τ↓ : Cell-el f↓ τ)
      → (E : (f↓₁ : Frm-el f) → Tree-el f↓₁ σ ≃ Cell-el f↓₁ τ)
      → Cell-el (f↓ ∥ σ↓ ▸ τ↓) E ↦ rel (E f↓) σ↓ τ↓
    {-# REWRITE Cell-𝕌↓ #-}

  --
  -- Primitive ap into the universe
  --
  
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
