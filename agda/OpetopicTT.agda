{-# OPTIONS --without-K --rewriting --type-in-type --no-positivity #-}

open import Base

module OpetopicTT where

  infixl 30 _∥_▸_ _∣_▸_
  
  data Frm : Set
  data Tree : Frm → Set
  data Pos : {f : Frm} → Tree f → Set
  data Cell : Frm → Set

  data Frm↓ : Frm → Set
  data Tree↓ : {f : Frm} → Tree f → Frm↓ f → Set
  data Pos↓ : {f : Frm} {σ : Tree f} → Pos σ → {f↓ : Frm↓ f} → Tree↓ σ f↓ → Set

  El : {f : Frm} (A : Cell f) (f↓ : Frm↓ f) → Set

  data Frm where
    ● : Frm 
    _∥_▸_ : (f : Frm) (σ : Tree f) (τ : Cell f) → Frm

  data Frm↓ where
    ∎ : Frm↓ ●
    _∣_▸_ : {f : Frm} {σ : Tree f} {τ : Cell f}
      → (f↓ : Frm↓ f) (σ↓ : Tree↓ σ f↓) (t : El τ f↓)
      → Frm↓ (f ∥ σ ▸ τ)

  Typ : {f : Frm} (σ : Tree f) (p : Pos σ) → Frm 
  Inh : {f : Frm} (σ : Tree f) (p : Pos σ) → Cell (Typ σ p)

  Typ↓ : {f : Frm} {σ : Tree f} {p : Pos σ}
    → {f↓ : Frm↓ f} (σ↓ : Tree↓ σ f↓) (p↓ : Pos↓ p σ↓)
    → Frm↓ (Typ σ p)

  Inh↓ : {f : Frm} {σ : Tree f} {p : Pos σ}
    → {f↓ : Frm↓ f} (σ↓ : Tree↓ σ f↓) (p↓ : Pos↓ p σ↓)
    → El (Inh σ p) (Typ↓ σ↓ p↓)

  η : {f : Frm} (A : Cell f)
    → Tree f

  η↓ : {f : Frm} {A : Cell f}
    → {f↓ : Frm↓ f} (a : El A f↓)
    → Tree↓ (η A) f↓ 

  μ : {f : Frm} (σ : Tree f)
    → (δ : (p : Pos σ) → Tree (Typ σ p))
    → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
    → Tree f

  μ↓ : {f : Frm} {σ : Tree f}
    → {δ : (p : Pos σ) → Tree (Typ σ p)}
    → {ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p)}
    → (f↓ : Frm↓ f) (σ↓ : Tree↓ σ f↓)
    → (δ↓ : (p : Pos σ) (p↓ : Pos↓ p σ↓) → Tree↓ (δ p) (Typ↓ σ↓ p↓))
    → (ε↓ : (p : Pos σ) (p↓ : Pos↓ p σ↓) → Tree↓ (ε p) (Typ↓ σ↓ p↓ ∣ δ↓ p p↓ ▸ Inh↓ σ↓ p↓))
    → Tree↓ (μ σ δ ε) f↓ 

  data Tree where
    nil : Tree ●
    cns : (A : Cell ●) (B : (a : El A ∎) → Tree ●) → Tree ● 

    lf : (f : Frm) (A : Cell f) → Tree (f ∥ η A ▸ A)
    nd : (f : Frm) (σ : Tree f) (τ : Cell f) (A : Cell (f ∥ σ ▸ τ))
       → (δ : (p : Pos σ) → Tree (Typ σ p))
       → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
       → Tree (f ∥ μ σ δ ε ▸ τ)

  data Pos where
    cns-here : {A : Cell ●} {B : (a : El A ∎) → Tree ●}
      → Pos (cns A B)
    cns-there : {A : Cell ●} {B : (a : El A ∎) → Tree ●}
      → (a : El A ∎) (p : Pos (B a))
      → Pos (cns A B)
      
    nd-here : {f : Frm} {σ : Tree f} {τ : Cell f} {A : Cell (f ∥ σ ▸ τ)}
       → {δ : (p : Pos σ) → Tree (Typ σ p)}
       → {ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p)}
       → Pos (nd f σ τ A δ ε)
    nd-there : {f : Frm} {σ : Tree f} {τ : Cell f} {A : Cell (f ∥ σ ▸ τ)}
       → {δ : (p : Pos σ) → Tree (Typ σ p)}
       → {ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p)}
       → (p : Pos σ) (q : Pos (ε p))
       → Pos (nd f σ τ A δ ε)

  data Cell where
    ⊤' : Cell ●
    Σ' : {f : Frm} → Tree f → Cell f

  data Tree↓ where
    nil↓ : Tree↓ nil ∎
    cns↓ : {A : Cell ●} {B : (a : El A ∎) → Tree ●}
      → (a : El A ∎) (b : Tree↓ (B a) ∎)
      → Tree↓ (cns A B) ∎
      
    lf↓ : (f : Frm) (A : Cell f)
      → (f↓ : Frm↓ f) (a : El A f↓)
      → Tree↓ (lf f A) (f↓ ∣ η↓ a ▸ a) 
    nd↓ : {f : Frm} {σ : Tree f} {τ : Cell f} {A : Cell (f ∥ σ ▸ τ)}
      → {δ : (p : Pos σ) → Tree (Typ σ p)}
      → {ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p)}
      → (f↓ : Frm↓ f) (σ↓ : Tree↓ σ f↓) (τ↓ : El τ f↓)
      → (δ↓ : (p : Pos σ) (p↓ : Pos↓ p σ↓) → Tree↓ (δ p) (Typ↓ σ↓ p↓))
      → (ε↓ : (p : Pos σ) (p↓ : Pos↓ p σ↓) → Tree↓ (ε p) (Typ↓ σ↓ p↓ ∣ δ↓ p p↓ ▸ Inh↓ σ↓ p↓))
      → Tree↓ (nd f σ τ A δ ε) (f↓ ∣ μ↓ f↓ σ↓ δ↓ ε↓ ▸ τ↓) 

  data Pos↓ where

  El ⊤' ∎ = ⊤
  El (Σ' σ) f↓ = Tree↓ σ f↓

  Typ .(cns _ _) cns-here = ●
  Typ .(cns _ _) (cns-there {B = B} a p) = Typ (B a) p
  Typ .(nd _ _ _ _ _ _) (nd-here {f} {σ} {τ}) = f ∥ σ ▸ τ
  Typ .(nd _ _ _ _ _ _) (nd-there {ε = ε} p q) = Typ (ε p) q
  
  Inh .(cns _ _) (cns-here {A}) = A
  Inh .(cns _ _) (cns-there {B = B} a p) = Inh (B a) p
  Inh .(nd _ _ _ _ _ _) (nd-here {A = A}) = A
  Inh .(nd _ _ _ _ _ _) (nd-there {ε = ε} p q) = Inh (ε p) q

  Typ↓ = {!!}
  Inh↓ = {!!}

  η = {!!}
  η↓ = {!!}

  μ = {!!}
  μ↓ = {!!}
