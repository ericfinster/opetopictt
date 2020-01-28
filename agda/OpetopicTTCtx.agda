{-# OPTIONS --without-K --rewriting --type-in-type --no-positivity #-}

open import Base

module OpetopicTTCtx where

  infixl 30 _∥_▸_  _∣_▸_
  
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

  η-pos : (f : Frm) (τ : Cell f)
    → Pos (η f τ)

  η↓ : {f : Frm} {τ : Cell f}
    → (f↓ : Frm↓ f) (τ↓ : Cell↓ τ f↓)
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

  γ : {f : Frm} (σ : Tree f) (τ : Cell f)
    → (ρ : Tree (f ∥ σ ▸ τ)) 
    → (δ : (p : Pos σ) → Tree (Typ σ p))
    → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
    → Tree (f ∥ μ f σ δ ε ▸ τ)

  Σ-cell : (f : Frm) (σ : Tree f) (τ : Cell f)
    → (θ : Cell (f ∥ σ ▸ τ))
    → (f↓ : Frm↓ f) (σ↓ : Tree↓ σ f↓)
    → Cell↓ τ f↓

  Σ-tree : (f : Frm) (σ : Tree f) (τ : Cell f)
    → (θ : Tree (f ∥ σ ▸ τ))
    → (f↓ : Frm↓ f) (σ↓ : Tree↓ σ f↓)
    → Cell↓ τ f↓

  data Cell where
    ⊤' : Cell ●
    Σ' : {f : Frm} (σ : Tree f) → Cell f
    W' : {f : Frm} (σ : Tree f) → Cell (f ∥ σ ▸ Σ' σ)
    -- There will probably be one more constructor for
    -- equivalences here ....

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

  Typ ._ (cns-here τ δ) = ●
  Typ ._ (cns-there τ δ p q) = Typ _ q
  Typ ._ (nd-here {f} {σ} {τ}) = f ∥ σ ▸ τ
  Typ ._ (nd-there p q) = Typ _ q
  
  Inh ._ (cns-here τ δ) = τ
  Inh ._ (cns-there τ δ p q) = Inh _ q
  Inh ._ (nd-here {A = A}) = A
  Inh ._ (nd-there p q) = Inh _ q

  data Cell↓ where
    ⊤↓ : Cell↓ ⊤' ∎
    Σ↓ : {f : Frm} {σ : Tree f}
      → (f↓ : Frm↓ f) (σ↓ : Tree↓ σ f↓)
      → Cell↓ (Σ' σ) f↓
    W↓ : {f : Frm} {σ : Tree f}
      → (f↓ : Frm↓ f) (σ↓ : Tree↓ σ f↓)
      → Cell↓ (W' σ) (f↓ ∣ σ↓ ▸ Σ↓ f↓ σ↓)

  data Tree↓ where
  
    nil↓ : Tree↓ nil ∎
    cns↓ : {τ : Cell ●} {δ : Cell↓ τ ∎ → Tree ●}
      → (τ↓ : Cell↓ τ ∎) (δ↓ : (τ↓ : Cell↓ τ ∎) → Tree↓ (δ τ↓) ∎)
      → Tree↓ (cns τ δ) ∎ 

    lf↓ : {f : Frm} {τ : Cell f}
      → (f↓ : Frm↓ f) (τ↓ : Cell↓ τ f↓)
      → Tree↓ (lf f τ) (f↓ ∣ η↓ f↓ τ↓ ▸ τ↓) 
    nd↓ : {f : Frm} {σ : Tree f} {τ : Cell f} {A : Cell (f ∥ σ ▸ τ)}
      → {δ : (p : Pos σ) → Tree (Typ σ p)}
      → {ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p)}
      → (f↓ : Frm↓ f) (σ↓ : Tree↓ σ f↓) (τ↓ : Cell↓ τ f↓) (a : Cell↓ A (f↓ ∣ σ↓ ▸ τ↓))
      → (δ↓ : (p : Pos σ) (p↓ : Pos↓ p σ↓) → Tree↓ (δ p) (Typ↓ σ↓ p↓))
      → (ε↓ : (p : Pos σ) (p↓ : Pos↓ p σ↓) → Tree↓ (ε p) (Typ↓ σ↓ p↓ ∣ δ↓ p p↓ ▸ Inh↓ σ↓ p↓))
      → Tree↓ (nd f σ τ A δ ε) (f↓ ∣ μ↓ f↓ σ↓ δ↓ ε↓ ▸ τ↓) 

  data Pos↓ where

    cns-here↓ : {τ : Cell ●} {δ : Cell↓ τ ∎ → Tree ●}
      → (τ↓ : Cell↓ τ ∎) (δ↓ : (τ↓ : Cell↓ τ ∎) → Tree↓ (δ τ↓) ∎)
      → Pos↓ (cns-here τ δ) (cns↓ τ↓ δ↓)
    cns-there↓ : {τ : Cell ●} {δ : Cell↓ τ ∎ → Tree ●}
      → {p : Cell↓ τ ∎} {q : Pos (δ p)}
      → (τ↓ : Cell↓ τ ∎) (δ↓ : (τ↓ : Cell↓ τ ∎) → Tree↓ (δ τ↓) ∎)
      → (q↓ : Pos↓ q (δ↓ p))
      → Pos↓ (cns-there τ δ p q) (cns↓ τ↓ δ↓)

    nd-here↓ : {f : Frm} {σ : Tree f} {τ : Cell f} {A : Cell (f ∥ σ ▸ τ)}
      → {δ : (p : Pos σ) → Tree (Typ σ p)}
      → {ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p)}
      → {f↓ : Frm↓ f} {σ↓ : Tree↓ σ f↓} {τ↓ : Cell↓ τ f↓} {a : Cell↓ A (f↓ ∣ σ↓ ▸ τ↓)}
      → {δ↓ : (p : Pos σ) (p↓ : Pos↓ p σ↓) → Tree↓ (δ p) (Typ↓ σ↓ p↓)}
      → {ε↓ : (p : Pos σ) (p↓ : Pos↓ p σ↓) → Tree↓ (ε p) (Typ↓ σ↓ p↓ ∣ δ↓ p p↓ ▸ Inh↓ σ↓ p↓)}
      → Pos↓ nd-here (nd↓ f↓ σ↓ τ↓ a δ↓ ε↓)
    nd-there↓ : {f : Frm} {σ : Tree f} {τ : Cell f} {A : Cell (f ∥ σ ▸ τ)}
      → {δ : (p : Pos σ) → Tree (Typ σ p)}
      → {ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p)}
      → {p : Pos σ} {q : Pos (ε p)}
      → {f↓ : Frm↓ f} {σ↓ : Tree↓ σ f↓} {τ↓ : Cell↓ τ f↓} {a : Cell↓ A (f↓ ∣ σ↓ ▸ τ↓)}
      → {δ↓ : (p : Pos σ) (p↓ : Pos↓ p σ↓) → Tree↓ (δ p) (Typ↓ σ↓ p↓)}
      → {ε↓ : (p : Pos σ) (p↓ : Pos↓ p σ↓) → Tree↓ (ε p) (Typ↓ σ↓ p↓ ∣ δ↓ p p↓ ▸ Inh↓ σ↓ p↓)}
      → (p↓ : Pos↓ p σ↓) (q↓ : Pos↓ q (ε↓ p p↓))
      → Pos↓ (nd-there p q) (nd↓ f↓ σ↓ τ↓ a δ↓ ε↓) 

  Typ↓ ._ (cns-here↓ τ↓ δ↓) = ∎
  Typ↓ ._ (cns-there↓ τ↓ δ↓ q↓) = Typ↓ _ q↓
  Typ↓ ._ (nd-here↓ {f↓ = f↓} {σ↓ = σ↓} {τ↓ = τ↓}) = f↓ ∣ σ↓ ▸ τ↓
  Typ↓ ._ (nd-there↓ p↓ q↓) = Typ↓ _ q↓

  Inh↓ ._ (cns-here↓ τ↓ δ↓) = τ↓
  Inh↓ ._ (cns-there↓ τ↓ δ↓ q↓) = Inh↓ _ q↓
  Inh↓ ._ (nd-here↓ {a = a}) = a
  Inh↓ ._ (nd-there↓ p↓ q↓) = Inh↓ _ q↓

  postulate

    -- η laws
    η-pos-typ : (f : Frm) (τ : Cell f)
      → (p : Pos (η f τ))
      → Typ (η f τ) p ↦ f
    {-# REWRITE η-pos-typ #-}

    η-pos-inh : (f : Frm) (τ : Cell f)
      → (p : Pos (η f τ))
      → Inh (η f τ) p ↦ τ
    {-# REWRITE η-pos-inh #-}
    
    -- μ laws
    μ-unit-r : (f : Frm) (σ : Tree f) 
      → μ f σ (λ p → η (Typ σ p) (Inh σ p)) (λ p → lf (Typ σ p) (Inh σ p)) ↦ σ
    {-# REWRITE μ-unit-r #-}

    μ-unit-l :  (f : Frm) (σ : Tree f) (τ : Cell f)
      → (δ : (p : Pos (η f τ)) → Tree f)
      → (ε : (p : Pos (η f τ)) → Tree (f ∥ δ p ▸ τ))
      → μ f (η f τ) δ ε ↦ δ (η-pos f τ)
    {-# REWRITE μ-unit-l #-}

    -- μ↓ laws
    μ↓-unit-r : (f : Frm) (σ : Tree f)
      → (f↓ : Frm↓ f) (σ↓ : Tree↓ σ f↓)
      → μ↓ f↓ σ↓ (λ p p↓ → η↓ (Typ↓ σ↓ p↓) (Inh↓ σ↓ p↓)) (λ p p↓ → lf↓ (Typ↓ σ↓ p↓) (Inh↓ σ↓ p↓)) ↦ σ↓ 
    {-# REWRITE μ↓-unit-r #-}
    
    -- This very general invariance principle seems to be necessary
    -- when μ depends on witnesses since otherwise, μ does not preserve
    -- the frame definitionally....
    μ-invar : (f : Frm) (σ : Tree f) 
      → (δ : (p : Pos σ) → Tree (Typ σ p))
      → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
      → (δ' : (p : Pos σ) (q : Pos (ε p)) → Tree (Typ (ε p) q))
      → (ε' : (p : Pos σ) (q : Pos (ε p)) → Tree (Typ (ε p) q ∥ δ' p q ▸ Inh (ε p) q))
      → μ f σ δ (λ p → μ (Typ σ p ∥ δ p ▸ Inh σ p) (ε p) (δ' p) (ε' p)) ↦ μ f σ δ ε
    {-# REWRITE μ-invar #-}

    --  Reduce unary composites ...
    Σ'-η : (f : Frm) (τ : Cell f)
      → Σ' (η f τ) ↦ τ
    {-# REWRITE Σ'-η #-}

    W'-η : (f : Frm) (τ : Cell f)
      → W' (η f τ) ↦ Σ' (lf f τ)
    {-# REWRITE W'-η #-}

  -- η : (f : Frm) (A : Cell f)
  --   → Tree f
  η ● A = cns A (λ _ → nil)
  η (f ∥ σ ▸ τ) A = 
    let η-dec p = η (Typ σ p) (Inh σ p)
        lf-dec p = lf (Typ σ p) (Inh σ p)
    in nd f σ τ A η-dec lf-dec

  -- η-pos : (f : Frm) (τ : Cell f)
  --   → Pos (η f τ)
  η-pos ● τ = cns-here τ _
  η-pos (f ∥ σ ▸ τ) θ = nd-here

  η↓ ∎ τ↓ = cns↓ τ↓ (λ _ → nil↓)
  η↓ (f↓ ∣ σ↓ ▸ τ↓) θ↓ = 
    let η-dec↓ p p↓ = η↓ (Typ↓ σ↓ p↓) (Inh↓ σ↓ p↓)
        lf-dec↓ p p↓ = lf↓ (Typ↓ σ↓ p↓) (Inh↓ σ↓ p↓)
    in nd↓ f↓ σ↓ τ↓ θ↓ η-dec↓ lf-dec↓

  γ-ctx : (Γ : Tree ●) (δ : (els : Tree↓ Γ ∎) → Tree ●) → Tree ●
  γ-ctx = {!!}

  -- μ : (f : Frm) (σ : Tree f) 
  --   → (δ : (p : Pos σ) → Tree (Typ σ p))
  --   → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
  --   → Tree f
  μ .● nil δ ε = nil
  μ .● (cns τ δ) δ' ε' =
    let Γ = δ' (cns-here τ δ)
        τ↓ r = Σ-tree ● Γ τ (ε' (cns-here τ δ)) ∎ r
        p↓ r q = cns-there τ δ (τ↓ r) q
        ψ r = μ ● (δ (τ↓ r)) (λ q → δ' (p↓ r q)) (λ q → ε' (p↓ r q))
    in γ-ctx Γ ψ
  μ .(f ∥ η f τ ▸ τ) (lf f τ) δ' ε' = lf f τ
  μ .(f ∥ μ f σ δ ε ▸ τ) (nd f σ τ θ δ ε) δ' ε' =
    let w = δ' nd-here
        δ'' p q = δ' (nd-there p q)
        ε'' p q = ε' (nd-there p q)
        ψ p = μ (Typ σ p ∥ δ p ▸ Inh σ p) (ε p) (δ'' p) (ε'' p) 
    in γ σ τ w δ ψ 

  μ↓ = {!!}

  -- γ : {f : Frm} (σ : Tree f) (τ : Cell f)
  --   → (ρ : Tree (f ∥ σ ▸ τ)) 
  --   → (δ : (p : Pos σ) → Tree (Typ σ p))
  --   → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
  --   → Tree (f ∥ μ f σ δ ε ▸ τ)
  γ .(η f τ) τ (lf f .τ) δ ε = ε (η-pos f τ)
  γ .(μ f ρ δ ε) τ (nd f ρ .τ θ δ ε) δ' ε' = {!!}


  -- γ .f .(η f τ) .τ (lf f τ) ϕ ψ = ψ (η-pos f τ)
  -- γ .f .(μ f σ δ) .τ (nd f σ τ α δ ε) ϕ ψ =
  --   let ϕ' p q = ϕ (μ-pos f σ δ p q)
  --       ψ' p q = ψ (μ-pos f σ δ p q)
  --       δ' p = μ (Typ f σ p) (δ p) (ϕ' p)
  --       ε' p = γ (Typ f σ p) (δ p) (Inh f σ p) (ε p) (ϕ' p) (ψ' p)
  --   in nd f σ τ α δ' ε'


  -- γ↓ = {!!}

  --
  --  These routines essentially correspond to "transporting"
  --  trees of elements along equivalences.  They compute by
  --  recursion on the tree/cell structure ...
  --
  
  Σ-cell f σ τ (Σ' θ) f↓ σ↓ = Σ-tree f σ τ θ f↓ σ↓
  Σ-cell f σ .(Σ' σ) (W' .σ) f↓ σ↓ = Σ↓ f↓ σ↓

  Σ-tree f .(η f τ) τ (lf .f .τ) f↓ σ↓ = Σ↓ f↓ σ↓
  Σ-tree f .(μ f σ δ ε) τ (nd .f σ .τ θ δ ε) f↓ σ↓ =
    Σ-cell f σ τ θ f↓ {!!}
