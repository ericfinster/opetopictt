{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Base

module Universe where

  data Frm : Set
  data Cell : Frm → Set
  data Tree : Frm → Set

  infixl 30 _∥_▸_
  
  data Frm where
    ● : Frm 
    _∥_▸_ : (f : Frm) (σ : Tree f) (τ : Cell f) → Frm

  data Cell where
    ⊤' : Cell ●

  Pos : {f : Frm} (σ : Tree f) → Set
  Typ : {f : Frm} (σ : Tree f) (p : Pos σ) → Frm 

  Inh : {f : Frm} (σ : Tree f) (p : Pos σ) → Cell (Typ σ p)

  η : {f : Frm} → Cell f → Tree f
  
  μ : {f : Frm} (σ : Tree f)
    → (κ : (p : Pos σ) → Tree (Typ σ p))
    → Tree f
  
  data Tree where
    ob : (A : Set) → Tree ● 
    lf : (f : Frm) (α : Cell f) → Tree (f ∥ η α ▸ α)
    nd : (f : Frm) (σ : Tree f) (τ : Cell f) (α : Cell (f ∥ σ ▸ τ))
       → (δ : (p : Pos σ) → Tree (Typ σ p))
       → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
       → Tree (f ∥ μ σ δ ▸ τ)

  Pos {●} (ob A) = A
  Pos {f ∥ σ ▸ τ} σ' = {!!}

  Typ {●} (ob A) a = ●
  Typ {f ∥ σ ▸ τ} σ' p = {!!}

  Inh {●} (ob A) a = ⊤'
  Inh {f ∥ σ ▸ τ} σ' p = {!!}

  η {●} ⊤' = ob ⊤
  η {f ∥ σ ▸ τ} α = {!!}

  μ {●} (ob A) κ = ob (Σ A (λ a → Pos (κ a)))
  μ {f ∥ σ₁ ▸ τ} σ κ = {!!}


