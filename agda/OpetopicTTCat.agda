{-# OPTIONS --without-K --rewriting --type-in-type --no-positivity #-}

open import Base

module OpetopicTTCat where

  infixl 30 _∥_▸_ _∣_▸_
  
  data Frm : Set
  data Tree : Frm → Set
  data Pos : {f : Frm} → Tree f → Set
  data Cell : Frm → Set

  data Frm↓ : Frm → Set
  data Tree↓ : {f : Frm} → Tree f → Frm↓ f → Set
  data Pos↓ : {f : Frm} {σ : Tree f} → Pos σ → {f↓ : Frm↓ f} → Tree↓ σ f↓ → Set
  data Cell↓ : {f : Frm} (A : Cell f) (f↓ : Frm↓ f) → Set

  data Frm where
    ● : Frm 
    _∥_▸_ : (f : Frm) (σ : Tree f) (τ : Cell f) → Frm

  data Frm↓ where
    ∎ : Frm↓ ●
    _∣_▸_ : {f : Frm} {σ : Tree f} {τ : Cell f}
      → (f↓ : Frm↓ f) (σ↓ : Tree↓ σ f↓) (t : Cell↓ τ f↓)
      → Frm↓ (f ∥ σ ▸ τ)

  Typ : {f : Frm} (σ : Tree f) (p : Pos σ) → Frm 
  Inh : {f : Frm} (σ : Tree f) (p : Pos σ) → Cell (Typ σ p)

  Typ↓ : {f : Frm} {σ : Tree f} {p : Pos σ}
    → {f↓ : Frm↓ f} (σ↓ : Tree↓ σ f↓) (p↓ : Pos↓ p σ↓)
    → Frm↓ (Typ σ p)

  Inh↓ : {f : Frm} {σ : Tree f} {p : Pos σ}
    → {f↓ : Frm↓ f} (σ↓ : Tree↓ σ f↓) (p↓ : Pos↓ p σ↓)
    → Cell↓ (Inh σ p) (Typ↓ σ↓ p↓)

  η : {f : Frm} (A : Cell f)
    → Tree f

  η↓ : {f : Frm} {A : Cell f}
    → {f↓ : Frm↓ f} (a : Cell↓ A f↓)
    → Tree↓ (η A) f↓ 

  μ : {f : Frm} (σ : Tree f)
    → (δ : (p : Pos σ) → Tree (Typ σ p))
    → Tree f

  μ↓ : {f : Frm} {σ : Tree f}
    → {δ : (p : Pos σ) → Tree (Typ σ p)}
    → (f↓ : Frm↓ f) (σ↓ : Tree↓ σ f↓)
    → (δ↓ : (p : Pos σ) (p↓ : Pos↓ p σ↓) → Tree↓ (δ p) (Typ↓ σ↓ p↓))
    → Tree↓ (μ σ δ) f↓ 

  γ : {f : Frm} (σ : Tree f) (τ : Cell f)
    → (ρ : Tree (f ∥ σ ▸ τ))
    → (ϕ : (p : Pos σ) → Tree (Typ σ p))
    → (ψ : (p : Pos σ) → Tree (Typ σ p ∥ ϕ p ▸ Inh σ p))
    → Tree (f ∥ μ σ ϕ ▸ τ)

  data Tree where
    ob : (A : Cell ●) → Tree ● 
    lf : (f : Frm) (A : Cell f) → Tree (f ∥ η A ▸ A)
    nd : (f : Frm) (σ : Tree f) (τ : Cell f) (A : Cell (f ∥ σ ▸ τ))
       → (δ : (p : Pos σ) → Tree (Typ σ p))
       → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
       → Tree (f ∥ μ σ δ ▸ τ)

  data Pos where
    ob-pos : {A : Cell ●} (a : Cell↓ A ∎) → Pos (ob A)
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
    π' : (A : Cell ●) → Cell (● ∥ ob A ▸ ⊤')
    Σ' : {f : Frm} {σ : Tree f} {τ : Cell f}
      → Tree (f ∥ σ ▸ τ) → Cell (f ∥ σ ▸ τ)
    -- There's also the "higher cell" for the composite...
    -- And you'll similarly have to define its "elements"...

  data Tree↓ where
    ob↓ : (A : Cell ●) (a : Cell↓ A ∎) → Tree↓ (ob A) ∎
    lf↓ : (f : Frm) (A : Cell f)
      → (f↓ : Frm↓ f) (a : Cell↓ A f↓)
      → Tree↓ (lf f A) (f↓ ∣ η↓ a ▸ a) 
    nd↓ : {f : Frm} {σ : Tree f} {τ : Cell f} {A : Cell (f ∥ σ ▸ τ)}
      → {δ : (p : Pos σ) → Tree (Typ σ p)}
      → {ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p)}
      → (f↓ : Frm↓ f) (σ↓ : Tree↓ σ f↓) (τ↓ : Cell↓ τ f↓)
      → (δ↓ : (p : Pos σ) (p↓ : Pos↓ p σ↓) → Tree↓ (δ p) (Typ↓ σ↓ p↓))
      → (ε↓ : (p : Pos σ) (p↓ : Pos↓ p σ↓) → Tree↓ (ε p) (Typ↓ σ↓ p↓ ∣ δ↓ p p↓ ▸ Inh↓ σ↓ p↓))
      → Tree↓ (nd f σ τ A δ ε) (f↓ ∣ μ↓ f↓ σ↓ δ↓ ▸ τ↓) 

  data Pos↓ where

  data Cell↓ where
    ⊤↓ : Cell↓ ⊤' ∎
    π↓ : (A : Cell ●) (a : Cell↓ A ∎) → Cell↓ (π' A) (∎ ∣ ob↓ A a  ▸ ⊤↓) 
    Σ↓ : {f : Frm} {σ : Tree f} {τ : Cell f} (θ : Tree (f ∥ σ ▸ τ))
      → (f↓ : Frm↓ f) (σ↓ : Tree↓ σ f↓) (τ↓ : Cell↓ τ f↓)
      → (θ↓ : Tree↓ θ (f↓ ∣ σ↓ ▸ τ↓))
      → Cell↓ (Σ' θ) (f↓ ∣ σ↓ ▸ τ↓)

  Typ .(ob _) (ob-pos a) = ●
  Typ .(nd _ _ _ _ _ _) (nd-here {f} {σ} {τ}) = f ∥ σ ▸ τ
  Typ .(nd _ _ _ _ _ _) (nd-there p q) = Typ _ q
  
  Inh .(ob _) (ob-pos a) = ⊤'
  Inh .(nd _ _ _ _ _ _) (nd-here {A = A}) = A
  Inh .(nd _ _ _ _ _ _) (nd-there p q) = Inh _ q

  Typ↓ = {!!}
  Inh↓ = {!!}

  η = {!!}
  η↓ = {!!}

  μ = {!!}
  μ↓ = {!!}

  γ = {!!}

