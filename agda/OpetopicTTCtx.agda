{-# OPTIONS --without-K --rewriting --type-in-type --no-positivity #-}

open import Base

module OpetopicTTCtx where

  infixl 30 _∥_▸_  -- _∣_▸_
  
  data Frm : Set
  data Cell : Frm → Set
  data Tree : Frm → Set
  data Pos : {f : Frm} (σ : Tree f) → Set

  data Frm↓ : Frm → Set
  data Cell↓ : {f : Frm} (A : Cell f) (f↓ : Frm↓ f) → Set
  data Tree↓ : {f : Frm} → Tree f → Frm↓ f → Set
  data Pos↓ : {f : Frm} {σ : Tree f} → Pos σ → {f↓ : Frm↓ f} → Tree↓ σ f↓ → Set

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

  {-# TERMINATING #-}
  η : (f : Frm) (A : Cell f)
    → Tree f

  η↓ : {f : Frm} {τ : Cell f}
    → {f↓ : Frm↓ f} (τ↓ : Cell↓ τ f↓)
    → Tree↓ (η f τ) f↓ 

  μ : (f : Frm) (σ : Tree f) 
    → (δ : (p : Pos σ) → Tree (Typ σ p))
    → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
    → Tree f

  μ↓ : {f : Frm} {σ : Tree f}
    → {δ : (p : Pos σ) → Tree (Typ σ p)}
    → {ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p)}
    → (f↓ : Frm↓ f) (σ↓ : Tree↓ σ f↓)
    → (δ↓ : (p : Pos σ) (p↓ : Pos↓ p σ↓) → Tree↓ (δ p) (Typ↓ σ↓ p↓))
    → (ε↓ : (p : Pos σ) (p↓ : Pos↓ p σ↓) → Tree↓ (ε p) (Typ↓ σ↓ p↓ ∣ δ↓ p p↓ ▸ Inh↓ σ↓ p↓))
    → Tree↓ (μ f σ δ ε) f↓ 

  data Cell where
    ⊤' : Cell ●
    Σ' : {f : Frm} (σ : Tree f) → Cell f
    W' : {f : Frm} (σ : Tree f) → Cell (f ∥ σ ▸ Σ' σ)
    -- There will probably be one more constructor for
    -- equivalences here ....

  γ : {f : Frm} (σ : Tree f) (τ : Cell f)
    → (ρ : Tree (f ∥ σ ▸ τ)) 
    → (δ : (p : Pos σ) → Tree (Typ σ p))
    → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
    → Tree (f ∥ μ f σ δ ε ▸ τ)

  data Tree where
  
    nil : Tree ● 
    cns : (τ : Cell ●) (δ : Cell↓ τ ∎ → Tree ●) → Tree ● 

    lf : (f : Frm) (τ : Cell f) → Tree (f ∥ η f τ ▸ τ)
    nd : (f : Frm) (σ : Tree f) (τ : Cell f) (θ : Cell (f ∥ σ ▸ τ))
       → (δ : (p : Pos σ) → Tree (Typ σ p))
       → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
       → Tree (f ∥ μ f σ δ ε ▸ τ)

  data Pos where
  
    cns-here : (τ : Cell ●) (δ : Cell↓ τ ∎ → Tree ●)
      → Pos (cns τ δ)
    cns-there : (τ : Cell ●) (δ : Cell↓ τ ∎ → Tree ●)
      → (p : Cell↓ τ ∎) (q : Pos (δ p))
      → Pos (cns τ δ)
      
    nd-here : {f : Frm} {σ : Tree f} {τ : Cell f} {A : Cell (f ∥ σ ▸ τ)}
       → {δ : (p : Pos σ) → Tree (Typ σ p)}
       → {ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p)}
       → Pos (nd f σ τ A δ ε) 
    nd-there : {f : Frm} {σ : Tree f} {τ : Cell f} {A : Cell (f ∥ σ ▸ τ)}
       → {δ : (p : Pos σ) → Tree (Typ σ p)}
       → {ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p)}
       → (p : Pos σ) (q : Pos (ε p))
       → Pos (nd f σ τ A δ ε) 

  data Tree↓ where
  
    nil↓ : Tree↓ nil ∎
    cns : {τ : Cell ●} {δ : Cell↓ τ ∎ → Tree ●}
      → (τ↓ : Cell↓ τ ∎) (δ↓ : (τ↓ : Cell↓ τ ∎) → Tree↓ (δ τ↓) ∎)
      → Tree↓ (cns τ δ) ∎ 

    lf↓ : (f : Frm) (τ : Cell f)
      → (f↓ : Frm↓ f) (τ↓ : Cell↓ τ f↓)
      → Tree↓ (lf f τ) (f↓ ∣ η↓ τ↓ ▸ τ↓) 
    nd↓ : {f : Frm} {σ : Tree f} {τ : Cell f} {A : Cell (f ∥ σ ▸ τ)}
      → {δ : (p : Pos σ) → Tree (Typ σ p)}
      → {ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p)}
      → (f↓ : Frm↓ f) (σ↓ : Tree↓ σ f↓) (τ↓ : Cell↓ τ f↓)
      → (δ↓ : (p : Pos σ) (p↓ : Pos↓ p σ↓) → Tree↓ (δ p) (Typ↓ σ↓ p↓))
      → (ε↓ : (p : Pos σ) (p↓ : Pos↓ p σ↓) → Tree↓ (ε p) (Typ↓ σ↓ p↓ ∣ δ↓ p p↓ ▸ Inh↓ σ↓ p↓))
      → Tree↓ (nd f σ τ A δ ε) (f↓ ∣ μ↓ f↓ σ↓ δ↓ ε↓ ▸ τ↓) 

  data Pos↓ where

  data Cell↓ where
    ⊤↓ : Cell↓ ⊤' ∎
    Σ↓ : {f : Frm} {σ : Tree f}
      → (f↓ : Frm↓ f) (σ↓ : Tree↓ σ f↓)
      → Cell↓ (Σ' σ) f↓
    W↓ : {f : Frm} {σ : Tree f}
      → (f↓ : Frm↓ f) (σ↓ : Tree↓ σ f↓)
      → Cell↓ (W' σ) (f↓ ∣ σ↓ ▸ Σ↓ f↓ σ↓)

  Typ .(cns τ δ) (cns-here τ δ) = ●
  Typ .(cns τ δ) (cns-there τ δ p q) = Typ _ q
  Typ .(nd _ _ _ _ _ _) (nd-here {f} {σ} {τ}) = f ∥ σ ▸ τ
  Typ .(nd _ _ _ _ _ _) (nd-there p q) = Typ _ q
  
  Inh .(cns τ δ) (cns-here τ δ) = τ
  Inh .(cns τ δ) (cns-there τ δ p q) = Inh _ q
  Inh .(nd _ _ _ _ _ _) (nd-here {A = A}) = A
  Inh .(nd _ _ _ _ _ _) (nd-there p q) = Inh _ q

  Typ↓ = {!!}
  Inh↓ = {!!}

  postulate

    -- μ laws
    μ-unit-r : (f : Frm) (σ : Tree f) (τ : Cell f)
      → (θ : Cell (f ∥ σ ▸ τ))
      → μ f σ (λ p → η (Typ σ p) (Inh σ p)) (λ p → lf (Typ σ p) (Inh σ p)) ↦ σ
    {-# REWRITE μ-unit-r #-}

  -- η : (f : Frm) (A : Cell f)
  --   → Tree f
  η ● A = cns A (λ _ → nil)
  η (f ∥ σ ▸ τ) A = 
    let η-dec p = η (Typ σ p) (Inh σ p)
        lf-dec p = lf (Typ σ p) (Inh σ p)
    in nd f σ τ A η-dec lf-dec

  η↓ = {!!}

  γ-ctx : (Γ : Tree ●) (δ : (els : Tree↓ Γ ∎) → Tree ●) → Tree ●
  γ-ctx = {!!}
  
  -- μ : (f : Frm) (σ : Tree f) 
  --   → (δ : (p : Pos σ) → Tree (Typ σ p))
  --   → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
  --   → Tree f
  μ .● nil δ ε = nil
  μ .● (cns τ δ) δ' ε' =
    let Γ = δ' (cns-here τ δ)
    in γ-ctx Γ (λ els → μ ● (δ {!!})
               (λ q → δ' (cns-there τ δ {!!} q))
               (λ q → ε' (cns-there τ δ {!!} q)))
  μ .(f ∥ η f τ ▸ τ) (lf f τ) δ' ε' = lf f τ
  μ .(f ∥ μ f σ δ ε ▸ τ) (nd f σ τ θ δ ε) δ' ε' =
    let w = δ' nd-here
        δ'' p q = δ' (nd-there p q)
        ε'' p q = ε' (nd-there p q)
        ψ p = μ (Typ σ p ∥ δ p ▸ Inh σ p) (ε p) (δ'' p) (ε'' p) 
    in {! γ σ τ w δ ψ !}


  μ↓ = {!!}

  -- γ : {f : Frm} (σ : Tree f) (τ : Cell f)
  --   → (ρ : Tree (f ∥ σ ▸ τ)) 
  --   → (δ : (p : Pos σ) → Tree (Typ σ p))
  --   → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
  --   → Tree (f ∥ μ f σ δ ε ▸ τ)
  γ = {!!}
  -- γ↓ = {!!}

