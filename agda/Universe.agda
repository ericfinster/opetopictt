{-# OPTIONS --without-K --rewriting --type-in-type --no-positivity #-}

open import Base

module Universe where

  data Frm : Set
  data Cell : Frm → Set
  data Tree : Frm → Set
  data Nd : {f : Frm} → Tree f → Set
  data Lf : {f : Frm} → Tree f → Set  

  infixl 30 _∥_▸_
  
  data Frm where
    ● : Frm 
    _∥_▸_ : (f : Frm) (σ : Tree f) (τ : Cell f) → Frm

  Typ : {f : Frm} (σ : Tree f) (p : Nd σ) → Frm 
  Inh : {f : Frm} (σ : Tree f) (p : Nd σ) → Cell (Typ σ p)

  η : {f : Frm} → Cell f → Tree f
  
  μ : {f : Frm} (σ : Tree f)
    → (κ : (p : Nd σ) → Tree (Typ σ p))
    → Tree f

  data Cell where
    Σ' : {f : Frm} (σ : Tree f) → Cell f

  El : {f : Frm} (α : Cell f) → Set

  data Tree where
    ob : Tree ● 
    lf : (f : Frm) (α : Cell f) → Tree (f ∥ η α ▸ α)
    nd : (f : Frm) (σ : Tree f) (τ : Cell f) (α : Cell (f ∥ σ ▸ τ))
       → (δ : (p : Nd σ) → Tree (Typ σ p))
       → (ε : (p : Nd σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
       → Tree (f ∥ μ σ δ ▸ τ)
  
  data Nd where
    ob-nd : Nd ob
    nd-here : (f : Frm) (σ : Tree f) (τ : Cell f) (α : Cell (f ∥ σ ▸ τ))
            → (δ : (p : Nd σ) → Tree (Typ σ p))
            → (ε : (p : Nd σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
            → Nd (nd f σ τ α δ ε)
    nd-there : (f : Frm) (σ : Tree f) (τ : Cell f) (α : Cell (f ∥ σ ▸ τ))
             → (δ : (p : Nd σ) → Tree (Typ σ p))
             → (ε : (p : Nd σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
             → (e : El α) (p : Nd σ) (n : Nd (ε p)) 
             → Nd (nd f σ τ α δ ε)
             
  data Lf where
    lf-lf : (f : Frm) (α : Cell f) → Lf (lf f α)
    lf-nd : (f : Frm) (σ : Tree f) (τ : Cell f) (α : Cell (f ∥ σ ▸ τ))
          → (δ : (p : Nd σ) → Tree (Typ σ p))
          → (ε : (p : Nd σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
          → (e : El α) (p : Nd σ) (l : Lf (ε p)) 
          → Lf (nd f σ τ α δ ε)

  El {f} (Σ' σ) = Lf σ

  Typ {●} ob tt = ●
  Typ {f ∥ .(η τ) ▸ τ} (lf .f .τ) ()
  Typ {f ∥ .(μ σ δ) ▸ τ} (nd .f σ .τ α δ ε) (nd-here .f .σ .τ .α .δ .ε) = f ∥ σ ▸ τ
  Typ {f ∥ .(μ σ δ) ▸ τ} (nd .f σ .τ α δ ε) (nd-there .f .σ .τ .α .δ .ε e p q) = Typ (ε p) q

  Inh {●} ob tt = Σ' ob
  Inh {f ∥ .(η τ) ▸ τ} (lf .f .τ) ()
  Inh {f ∥ .(μ σ δ) ▸ τ} (nd .f σ .τ α δ ε) (nd-here .f .σ .τ .α .δ .ε) = α
  Inh {f ∥ .(μ σ δ) ▸ τ} (nd .f σ .τ α δ ε) (nd-there .f .σ .τ .α .δ .ε e p q) = Inh (ε p) q

  η {●} (Σ' σ) = σ
  η {f ∥ σ ▸ τ} α = {!nd f σ τ α ? ?!}

  -- η (f ∥ σ ▸ τ) α =  
  --   let η-dec p = η (Typ f σ p) (Inh f σ p)
  --       lf-dec p = lf (Typ f σ p) (Inh f σ p)
  --   in nd f σ τ α η-dec lf-dec

  μ {●} ob κ = κ ob-nd
  μ {f ∥ σ ▸ τ} σ' κ = {!!}


