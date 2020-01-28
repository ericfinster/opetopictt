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

  μ-pos : (f : Frm) (σ : Tree f) 
    → (δ : (p : Pos σ) → Tree (Typ σ p))
    → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
    → (p : Pos σ) (q : Pos (δ p))
    → Pos (μ f σ δ ε)
  
  μ-pos-fst : (f : Frm) (σ : Tree f) 
    → (δ : (p : Pos σ) → Tree (Typ σ p))
    → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
    → Pos (μ f σ δ ε) → Pos σ
  
  μ-pos-snd : (f : Frm) (σ : Tree f) 
    → (δ : (p : Pos σ) → Tree (Typ σ p))
    → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
    → (p : Pos (μ f σ δ ε)) → Pos (δ (μ-pos-fst f σ δ ε p))

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

  --  Here I'm putting new structure we haven't see before
  --  which need some name cleanup, renaming and ordering ....
  
  γ-ctx : (Γ : Tree ●) (δ : (els : Tree↓ Γ ∎) → Tree ●) → Tree ●

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

    -- μ-pos laws
    μ-pos-typ : (f : Frm) (σ : Tree f) 
      → (δ : (p : Pos σ) → Tree (Typ σ p))
      → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
      → (p : Pos (μ f σ δ ε))
      → Typ (μ f σ δ ε) p ↦ Typ (δ (μ-pos-fst f σ δ ε p)) (μ-pos-snd f σ δ ε p)
    {-# REWRITE μ-pos-typ #-}
    
    μ-pos-inh : (f : Frm) (σ : Tree f) 
      → (δ : (p : Pos σ) → Tree (Typ σ p))
      → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
      → (p : Pos (μ f σ δ ε))
      → Inh (μ f σ δ ε) p ↦ Inh (δ (μ-pos-fst f σ δ ε p)) (μ-pos-snd f σ δ ε p)
    {-# REWRITE μ-pos-inh #-}

    μ-pos-fst-β : (f : Frm) (σ : Tree f) 
      → (δ : (p : Pos σ) → Tree (Typ σ p))
      → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
      → (p : Pos σ) (q : Pos (δ p))
      → μ-pos-fst f σ δ ε (μ-pos f σ δ ε p q) ↦ p 
    {-# REWRITE μ-pos-fst-β #-}
    
    μ-pos-snd-β : (f : Frm) (σ : Tree f) 
      → (δ : (p : Pos σ) → Tree (Typ σ p))
      → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
      → (p : Pos σ) (q : Pos (δ p))
      → μ-pos-snd f σ δ ε (μ-pos f σ δ ε p q) ↦ q
    {-# REWRITE μ-pos-snd-β #-}

    μ-pos-η : (f : Frm) (σ : Tree f) 
      → (δ : (p : Pos σ) → Tree (Typ σ p))
      → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
      → (p : Pos (μ f σ δ ε))
      → μ-pos f σ δ ε (μ-pos-fst f σ δ ε p) (μ-pos-snd f σ δ ε p) ↦ p
    {-# REWRITE μ-pos-η #-}

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


    -- Interesting.  We already need invariance for associativity to make sense....
    -- And the current version doesn't yet capture what is needed, meaning that
    -- γ still can't typecheck.  So we've got a bit of work left to figure this
    -- part out ....
    μ-assoc : (f : Frm) (σ : Tree f) (τ : Cell f)
      → (δ : (p : Pos σ) → Tree (Typ σ p))
      → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
      → (δ' : (p : Pos (μ f σ δ ε)) → Tree (Typ (δ (μ-pos-fst f σ δ ε p)) (μ-pos-snd f σ δ ε p)))
      → (ε' : (p : Pos (μ f σ δ ε)) → Tree (Typ (δ (μ-pos-fst f σ δ ε p)) (μ-pos-snd f σ δ ε p) ∥ δ' p ▸ Inh (δ (μ-pos-fst f σ δ ε p)) (μ-pos-snd f σ δ ε p)))
      → μ f (μ f σ δ ε) δ' ε' ↦ μ f σ (λ p → μ (Typ σ p) (δ p) (λ q → δ' (μ-pos f σ δ ε p q)) (λ q → ε' (μ-pos f σ δ ε p q)))
                                      (λ p → {!μ (Typ σ p ∥ δ p ▸ Inh σ p) (ε p) ? ? !})

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

  μ-pos = {!!}
  μ-pos-fst = {!!}
  μ-pos-snd = {!!}

  μ↓ = {!!}

  -- γ : {f : Frm} (σ : Tree f) (τ : Cell f)
  --   → (ρ : Tree (f ∥ σ ▸ τ)) 
  --   → (δ : (p : Pos σ) → Tree (Typ σ p))
  --   → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
  --   → Tree (f ∥ μ f σ δ ε ▸ τ)
  γ .(η f τ) τ (lf f .τ) δ ε = ε (η-pos f τ)
  γ .(μ f σ δ₀ ε₀) τ (nd f σ .τ θ δ₀ ε₀) δ₁ ε₁ = {!!}
    -- let δ₁' p q = δ₁ (μ-pos f σ δ₀ ε₀ p q)
    --     ε₁' p q = ε₁ (μ-pos f σ δ₀ ε₀ p q)
    --     δ₀' p = μ (Typ σ p) (δ₀ p) (δ₁' p) (ε₁' p)
    --     ε₀' p = γ {f = Typ σ p} (δ₀ p) (Inh σ p) (ε₀ p) (δ₁' p) (ε₁' p)
    -- in nd f σ τ θ δ₀' ε₀'
    
  -- γ↓ = {!!}

  γ-ctx = {!!}

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
