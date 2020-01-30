{-# OPTIONS --without-K --rewriting --type-in-type --no-positivity #-}

module OpetopicAgda where

  infixl 30 _∥_▸_  -- _∣_▸_

  data Ctx : Set where
    nil : Ctx
    cns : (A : Set) (B : A → Ctx) → Ctx

  data CtxPos : Ctx → Set where
    cns-here : (A : Set) (B : A → Ctx) → CtxPos (cns A B)
    cns-there : (A : Set) (B : A → Ctx)
      → (a : A) (p : CtxPos (B a))
      → CtxPos (cns A B)

  CtxTyp : (Γ : Ctx) (p : CtxPos Γ) → Set
  CtxTyp .(cns A B) (cns-here A B) = A
  CtxTyp .(cns A B) (cns-there A B a p) = CtxTyp (B a) p

  data Σ↓ : Ctx → Set where
    nil↓ : Σ↓ nil
    cns↓ : {A : Set} {B : A → Ctx}
      → (a : A) (b : Σ↓ (B a))
      → Σ↓ (cns A B)

  data Frm : Set
  data Tree : Frm → Set
  data Pos : {f : Frm} (σ : Tree f) → Set

  data Frm↓ : Frm → Set 
  data Tree↓ : {f : Frm} (f↓ : Frm↓ f) → Tree f → Set where
  data Pos↓ : {f : Frm} {f↓ : Frm↓ f} {σ : Tree f} → Tree↓ f↓ σ → Pos σ → Set where

  Cell : Frm → Set 
  Cell↓ : {f : Frm} (f↓ : Frm↓ f) (A : Cell f) → Set

  data Frm where
    ● : (Γ : Ctx) (A : Set) → Frm
    _∥_▸_ : (f : Frm) (σ : Tree f) (τ : Cell f) → Frm

  data Frm↓ where
    ∎ : {Γ : Ctx} {A : Set}
      → (g : Σ↓ Γ) (a : A)
      → Frm↓ (● Γ A)
    _∣_▸_ : {f : Frm} {σ : Tree f} {τ : Cell f}
      → (f↓ : Frm↓ f) (σ↓ : Tree↓ f↓ σ) (t : Cell↓ f↓ τ)
      → Frm↓ (f ∥ σ ▸ τ)

  record CtxCell (Γ : Ctx) (A : Set) : Set where
    field
      CtxRel : Σ↓ Γ → A → Set

  open CtxCell
  
  record EqvCell (f : Frm) (σ : Tree f) (τ : Cell f) : Set where
    field
      EqvRel : {f↓ : Frm↓ f} → Tree↓ f↓ σ → Cell↓ f↓ τ → Set

  open EqvCell
  
  Cell (● Γ A) = CtxCell Γ A
  Cell (f ∥ σ ▸ τ) = EqvCell f σ τ

  Cell↓ {● Γ A} (∎ g a) C = CtxRel C g a
  Cell↓ {f ∥ σ ▸ τ} (f↓ ∣ σ↓ ▸ τ↓) C = EqvRel C σ↓ τ↓

  Typ : {f : Frm} (σ : Tree f) (p : Pos σ) → Frm
  Inh : {f : Frm} (σ : Tree f) (p : Pos σ) → Cell (Typ σ p)

  η : (f : Frm) (A : Cell f)
    → Tree f

  μ : (f : Frm) (σ : Tree f) 
    → (δ : (p : Pos σ) → Tree (Typ σ p))
    → Tree f

  μ-ctx : (Γ : Ctx) 
    → (δ : (p : CtxPos Γ) → Ctx)
    → (ε : (p : CtxPos Γ) → Tree (● (δ p) (CtxTyp Γ p)))
    → Ctx
  μ-ctx = {!!}
  
  data Tree where
    lf-ctx : (A : Set) → Tree (● (cns A (λ _ → nil)) A)
    nd-ctx : (Γ : Ctx) (A : Set) (C : CtxCell Γ A)
      → (δ : (p : CtxPos Γ) → Ctx)
      → (ε : (p : CtxPos Γ) → Tree (● (δ p) (CtxTyp Γ p)))
      → Tree (● (μ-ctx Γ δ ε) A)

    lf : (f : Frm) (τ : Cell f) → Tree (f ∥ η f τ ▸ τ)
    nd : (f : Frm) (σ : Tree f) (τ : Cell f) (C : EqvCell f σ τ)
       → (δ : (p : Pos σ) → Tree (Typ σ p))
       → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
       → Tree (f ∥ μ f σ δ ▸ τ)
  
  data Pos where


  Typ = {!!}
  Inh = {!!}

  η = {!!}
  μ = {!!}
