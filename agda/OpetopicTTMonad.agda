{-# OPTIONS --without-K --rewriting --type-in-type --no-positivity #-}

open import Base

module OpetopicTTMonad where

  infixl 30 _∥_▸_  -- _∣_▸_

  data Frm : Set
  data Tree : Frm → Set
  data Cell : Frm → Set

  -- data Frm↓ : Frm → Set
  -- data Tree↓ : {f : Frm} → Tree f → Frm↓ f → Set
  -- data Pos↓ : {f : Frm} {σ : Tree f} → Pos σ → {f↓ : Frm↓ f} → Tree↓ σ f↓ → Set
  -- data Cell↓ : {f : Frm} (A : Cell f) (f↓ : Frm↓ f) → Set

  data Frm where
    ● : Frm 
    _∥_▸_ : (f : Frm) (σ : Tree f) (τ : Cell f) → Frm

  data Pos : {f : Frm} (σ : Tree f) (τ : Cell f) (θ : Cell (f ∥ σ ▸ τ)) → Set

  -- data Frm↓ where
  --   ∎ : Frm↓ ●
  --   _∣_▸_ : {f : Frm} {σ : Tree f} {τ : Cell f}
  --     → (f↓ : Frm↓ f) (σ↓ : Tree↓ σ f↓) (t : Cell↓ τ f↓)
  --     → Frm↓ (f ∥ σ ▸ τ)

  Typ : {f : Frm} (σ : Tree f) (τ : Cell f)
    → (θ : Cell (f ∥ σ ▸ τ)) (p : Pos σ τ θ)
    → Frm
    
  Inh : {f : Frm} (σ : Tree f) (τ : Cell f)
    → (θ : Cell (f ∥ σ ▸ τ)) (p : Pos σ τ θ)
    → Cell (Typ σ τ θ p)

  -- Typ↓ : {f : Frm} {σ : Tree f} {p : Pos σ}
  --   → {f↓ : Frm↓ f} (σ↓ : Tree↓ σ f↓) (p↓ : Pos↓ p σ↓)
  --   → Frm↓ (Typ σ p)

  -- Inh↓ : {f : Frm} {σ : Tree f} {p : Pos σ}
  --   → {f↓ : Frm↓ f} (σ↓ : Tree↓ σ f↓) (p↓ : Pos↓ p σ↓)
  --   → Cell↓ (Inh σ p) (Typ↓ σ↓ p↓)

  η : {f : Frm} (A : Cell f)
    → Tree f

  -- η↓ : {f : Frm} {A : Cell f}
  --   → {f↓ : Frm↓ f} (a : Cell↓ A f↓)
  --   → Tree↓ (η A) f↓ 

  μ : {f : Frm} (σ : Tree f) (τ : Cell f)
    → (θ : Cell (f ∥ σ ▸ τ))
    → (δ : (p : Pos σ τ θ) → Tree (Typ σ τ θ p))
    → Tree f

  -- μ↓ : {f : Frm} {σ : Tree f}
  --   → {δ : (p : Pos σ) → Tree (Typ σ p)}
  --   → (f↓ : Frm↓ f) (σ↓ : Tree↓ σ f↓)
  --   → (δ↓ : (p : Pos σ) (p↓ : Pos↓ p σ↓) → Tree↓ (δ p) (Typ↓ σ↓ p↓))
  --   → Tree↓ (μ σ δ) f↓ 

  -- γ : {f : Frm} (σ : Tree f) (τ : Cell f)
  --   → (ρ : Tree (f ∥ σ ▸ τ))
  --   → (ϕ : (p : Pos σ {!!} {!!}) → Tree (Typ σ p))
  --   → (ψ : (p : Pos σ {!!} {!!}) → Tree (Typ σ p ∥ ϕ p ▸ Inh σ p))
  --   → Tree (f ∥ μ σ ϕ ▸ τ)

  data Cell where
    ⊤' : Cell ●
    Σ' : {f : Frm} {σ : Tree f} {τ : Cell f}
      → Tree (f ∥ σ ▸ τ) → Cell (f ∥ σ ▸ τ)
    W' : {f : Frm} {σ : Tree f} {τ : Cell f}
      → (θ : Tree (f ∥ σ ▸ τ))
      → Cell (f ∥ σ ▸ τ ∥ θ ▸ Σ' θ)

  data Tree where
    ob : Tree ● 
    lf : (f : Frm) (A : Cell f) → Tree (f ∥ η A ▸ A)
    nd : (f : Frm) (σ : Tree f) (τ : Cell f) (θ : Cell (f ∥ σ ▸ τ))
       → (δ : (p : Pos σ τ θ) → Tree (Typ σ τ θ p))
       → (ε : (p : Pos σ τ θ) → Tree (Typ σ τ θ p ∥ δ p ▸ Inh σ τ θ p))
       → Tree (f ∥ μ σ τ θ δ ▸ τ)

  -- The universe now consists of arrow contstructors ...
  𝕌 : Set
  𝕌 = Cell (● ∥ ob ▸ ⊤')

  El : 𝕌 → Set
  El = {!!}

  data Pos where
    ob-pos : (A : 𝕌) (a : El A) → Pos ob ⊤' A
    nd-here : {f : Frm} {σ : Tree f} {τ : Cell f} {A : Cell (f ∥ σ ▸ τ)}
       → {δ : (p : Pos σ τ A) → Tree (Typ σ τ A p)}
       → {ε : (p : Pos σ τ A) → Tree (Typ σ τ A p ∥ δ p ▸ Inh σ τ A p)}
       → Pos (nd f σ τ A δ ε) (Σ' (nd f σ τ A δ ε)) (W' (nd f σ τ A δ ε))
    nd-there : {f : Frm} {σ : Tree f} {τ : Cell f} {A : Cell (f ∥ σ ▸ τ)}
       → {δ : (p : Pos σ τ A) → Tree (Typ σ τ A p)}
       → {ε : (p : Pos σ τ A) → Tree (Typ σ τ A p ∥ δ p ▸ Inh σ τ A p)}
       → (p : Pos σ τ A) (q : Pos (ε p) (Σ' (ε p)) (W' (ε p)))
       → Pos (nd f σ τ A δ ε) (Σ' (nd f σ τ A δ ε)) (W' (nd f σ τ A δ ε))

  -- data Tree↓ where
  --   ob↓ : (A : Cell ●) (a : Cell↓ A ∎) → Tree↓ (ob A) ∎
  --   lf↓ : (f : Frm) (A : Cell f)
  --     → (f↓ : Frm↓ f) (a : Cell↓ A f↓)
  --     → Tree↓ (lf f A) (f↓ ∣ η↓ a ▸ a) 
  --   nd↓ : {f : Frm} {σ : Tree f} {τ : Cell f} {A : Cell (f ∥ σ ▸ τ)}
  --     → {δ : (p : Pos σ) → Tree (Typ σ p)}
  --     → {ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p)}
  --     → (f↓ : Frm↓ f) (σ↓ : Tree↓ σ f↓) (τ↓ : Cell↓ τ f↓)
  --     → (δ↓ : (p : Pos σ) (p↓ : Pos↓ p σ↓) → Tree↓ (δ p) (Typ↓ σ↓ p↓))
  --     → (ε↓ : (p : Pos σ) (p↓ : Pos↓ p σ↓) → Tree↓ (ε p) (Typ↓ σ↓ p↓ ∣ δ↓ p p↓ ▸ Inh↓ σ↓ p↓))
  --     → Tree↓ (nd f σ τ A δ ε) (f↓ ∣ μ↓ f↓ σ↓ δ↓ ▸ τ↓) 

  -- data Pos↓ where

  -- data Cell↓ where
  --   ⊤↓ : Cell↓ ⊤' ∎
  --   π↓ : (A : Cell ●) (a : Cell↓ A ∎) → Cell↓ (π' A) (∎ ∣ ob↓ A a  ▸ ⊤↓) 
  --   Σ↓ : {f : Frm} {σ : Tree f} {τ : Cell f} (θ : Tree (f ∥ σ ▸ τ))
  --     → (f↓ : Frm↓ f) (σ↓ : Tree↓ σ f↓) (τ↓ : Cell↓ τ f↓)
  --     → (θ↓ : Tree↓ θ (f↓ ∣ σ↓ ▸ τ↓))
  --     → Cell↓ (Σ' θ) (f↓ ∣ σ↓ ▸ τ↓)

  Typ = {!!}
  Inh = {!!}

  -- Typ↓ = {!!}
  -- Inh↓ = {!!}

  η = {!!}
  -- η↓ = {!!}

  μ = {!!}
  -- μ↓ = {!!}

  -- γ = {!!}

