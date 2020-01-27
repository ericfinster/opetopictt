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

  data Pos : {f : Frm} (σ : Tree f) (τ : Cell f)
    → (θ : Cell (f ∥ σ ▸ τ)) → Set

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

  {-# TERMINATING #-}
  η : (f : Frm) (A : Cell f)
    → Tree f

  -- η↓ : {f : Frm} {A : Cell f}
  --   → {f↓ : Frm↓ f} (a : Cell↓ A f↓)
  --   → Tree↓ (η A) f↓ 

  μ : (f : Frm) (σ : Tree f) (τ : Cell f)
    → (θ : Cell (f ∥ σ ▸ τ))
    → (δ : (p : Pos σ τ θ) → Tree (Typ σ τ θ p))
    → Tree f

  -- μ↓ : {f : Frm} {σ : Tree f}
  --   → {δ : (p : Pos σ) → Tree (Typ σ p)}
  --   → (f↓ : Frm↓ f) (σ↓ : Tree↓ σ f↓)
  --   → (δ↓ : (p : Pos σ) (p↓ : Pos↓ p σ↓) → Tree↓ (δ p) (Typ↓ σ↓ p↓))
  --   → Tree↓ (μ σ δ) f↓ 

  data Cell where
    ⊤' : Cell ●
    Σ' : {f : Frm} {σ : Tree f} {τ : Cell f}
      → Tree (f ∥ σ ▸ τ) → Cell (f ∥ σ ▸ τ)
    W' : {f : Frm} {σ : Tree f} {τ : Cell f}
      → (θ : Tree (f ∥ σ ▸ τ))
      → Cell (f ∥ σ ▸ τ ∥ θ ▸ Σ' θ)
    -- There will probably be one more constructor for
    -- equivalences here ....

  γ : {f : Frm} (σ : Tree f) (τ : Cell f)
    → (ρ : Tree (f ∥ σ ▸ τ)) (M : Cell (f ∥ σ ▸ τ))
    → (ϕ : (p : Pos σ τ M) → Tree (Typ σ τ M p))
    → (ψ : (p : Pos σ τ M) → Tree (Typ σ τ M p ∥ ϕ p ▸ Inh σ τ M p))
    → Tree (f ∥ μ f σ τ M ϕ ▸ τ)

  data Tree where
    ob : Tree ● 
    lf : (f : Frm) (A : Cell f) → Tree (f ∥ η f A ▸ A)
    nd : (f : Frm) (σ : Tree f) (τ : Cell f) (θ : Cell (f ∥ σ ▸ τ))
       → (δ : (p : Pos σ τ θ) → Tree (Typ σ τ θ p))
       → (ε : (p : Pos σ τ θ) → Tree (Typ σ τ θ p ∥ δ p ▸ Inh σ τ θ p))
       → Tree (f ∥ μ f σ τ θ δ ▸ τ)

  -- The *arrows* now play the role of the universe, as
  -- I would have expected ...
  𝕌 : Set
  𝕌 = Cell (● ∥ ob ▸ ⊤')

  El : 𝕌 → Set
  El = {!!}

  data Pos where
    ob-pos : (A : 𝕌) (a : El A) → Pos ob ⊤' A
    nd-here : {f : Frm} {σ : Tree f} {τ : Cell f} {A : Cell (f ∥ σ ▸ τ)}
       → {δ : (p : Pos σ τ A) → Tree (Typ σ τ A p)}
       → {ε : (p : Pos σ τ A) → Tree (Typ σ τ A p ∥ δ p ▸ Inh σ τ A p)}
       → (Χ : Cell (f ∥ μ f σ τ A δ ▸ τ))
       → (Ω : Cell (f ∥ μ f σ τ A δ ▸ τ ∥ nd f σ τ A δ ε ▸ Χ))
       → Pos (nd f σ τ A δ ε) Χ Ω
    nd-there : {f : Frm} {σ : Tree f} {τ : Cell f} {A : Cell (f ∥ σ ▸ τ)}
       → {δ : (p : Pos σ τ A) → Tree (Typ σ τ A p)}
       → {ε : (p : Pos σ τ A) → Tree (Typ σ τ A p ∥ δ p ▸ Inh σ τ A p)}
       → (p : Pos σ τ A)
       → (M : Cell (Typ σ τ A p ∥ δ p ▸ Inh σ τ A p))
       → (N : Cell (Typ σ τ A p ∥ δ p ▸ Inh σ τ A p ∥ ε p ▸ M))
       → (q : Pos (ε p) M N)
       → (O : Cell (f ∥ μ f σ τ A δ ▸ τ))
       → (P : Cell (f ∥ μ f σ τ A δ ▸ τ ∥ nd f σ τ A δ ε ▸ O))
       → Pos (nd f σ τ A δ ε) O P

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

  Typ .ob .⊤' θ (ob-pos .θ a) = ●
  Typ .(nd _ _ _ _ _ _) τ' θ' (nd-here {f} {σ} {τ} .τ' .θ') = f ∥ σ ▸ τ
  Typ .(nd _ _ _ _ _ _) τ' θ' (nd-there p M N q .τ' .θ') = Typ _ _ _ q

  Inh .ob .⊤' θ (ob-pos .θ a) = ⊤'
  Inh .(nd _ _ _ _ _ _) τ' θ' (nd-here {A = A} .τ' .θ') = A
  Inh .(nd _ _ _ _ _ _) τ' θ' (nd-there p M N q .τ' .θ') = Inh _ _ _ q

  -- Typ↓ = {!!}
  -- Inh↓ = {!!}

  postulate

    -- μ laws
    μ-unit-r : (f : Frm) (σ : Tree f) (τ : Cell f)
      → (θ : Cell (f ∥ σ ▸ τ))
      → μ f σ τ θ (λ p → η (Typ σ τ θ p) (Inh σ τ θ p)) ↦ σ
    {-# REWRITE μ-unit-r #-}


  -- η : {f : Frm} (A : Cell f)
  --   → Tree f
  η ● A = ob
  η (f ∥ σ ▸ τ) A = 
    let η-dec p = η (Typ σ τ A p) (Inh σ τ A p)
        lf-dec p = lf (Typ σ τ A p) (Inh σ τ A p)
    in nd f σ τ A η-dec lf-dec

  η-pos : (f : Frm) (A : Cell f)
    → (B : Cell f) (M : Cell (f ∥ η f A ▸ B))
    → Pos (η f A) B M 
  η-pos ● ⊤' ⊤' A = ob-pos A {!!} -- ob-pos _ {!!}
  η-pos (f ∥ σ ▸ τ) A B M = nd-here B M -- nd-here A (Σ' (lf (f ∥ σ ▸ τ) A))

  -- η↓ = {!!}

  -- μ : (f : Frm) (σ : Tree f) (τ : Cell f)
  --   → (θ : Cell (f ∥ σ ▸ τ))
  --   → (δ : (p : Pos σ τ θ) → Tree (Typ σ τ θ p))
  --   → Tree f
  μ .● ob τ θ δ = ob
  μ .(f ∥ η f A ▸ A) (lf f A) τ θ δ = lf f A
  μ .(f ∥ μ f σ τ θ δ ▸ τ) (nd f σ τ θ δ ε) τ' θ' δ' = 
    let w = δ' (nd-here τ' θ')
        δ'' p q = δ' (nd-there p (Σ' (ε p)) (W' (ε p)) q τ' θ')
        ψ p = μ (Typ σ τ θ p ∥ δ p ▸ Inh σ τ θ p) (ε p) (Σ' (ε p)) (W' (ε p)) (δ'' p)
    in γ σ τ w θ δ ψ 

  -- μ↓ = {!!}

  -- γ : {f : Frm} (σ : Tree f) (τ : Cell f)
  --   → (ρ : Tree (f ∥ σ ▸ τ)) (M : Cell (f ∥ σ ▸ τ))
  --   → (ϕ : (p : Pos σ τ M) → Tree (Typ σ τ M p))
  --   → (ψ : (p : Pos σ τ M) → Tree (Typ σ τ M p ∥ ϕ p ▸ Inh σ τ M p))
  --   → Tree (f ∥ μ f σ τ M ϕ ▸ τ)
  γ .(η f τ) τ (lf f .τ) M ϕ ψ = {!!}
  γ .(μ f ρ τ θ δ) τ (nd f ρ .τ θ δ ε) M ϕ ψ = {!!}


  -- γ .f .(η f τ) .τ (lf f τ) ϕ ψ = ψ (η-pos f τ)
  -- γ .f .(μ f σ δ) .τ (nd f σ τ α δ ε) ϕ ψ =
  --   let ϕ' p q = ϕ (μ-pos f σ δ p q)
  --       ψ' p q = ψ (μ-pos f σ δ p q)
  --       δ' p = μ (Typ f σ p) (δ p) (ϕ' p)
  --       ε' p = γ (Typ f σ p) (δ p) (Inh f σ p) (ε p) (ϕ' p) (ψ' p)
  --   in nd f σ τ α δ' ε'

  -- γ↓ = {!!}

  --
  --  The Opetopic elimination principles.
  --

  -- elim : (f : Frm) (σ : Tree f) (τ : Cell f)
  --   → (θ : Tree (f ∥ σ ▸ τ))
  --   → (A : Cell (f ∥ σ ▸ τ)) (B : Cell (f ∥ σ ▸ τ ∥ θ ▸ A))
  --   → Cell (f ∥ σ ▸ τ ∥ η (f ∥ σ ▸ τ) (Σ' θ) ▸ A) 
  -- elim f σ τ θ A B = {!!}

  -- comp : (f : Frm) (σ : Tree f) (τ : Cell f)
  --   → (θ : Tree (f ∥ σ ▸ τ))
  --   → (A : Cell (f ∥ σ ▸ τ)) (B : Cell (f ∥ σ ▸ τ ∥ θ ▸ A))
  --   → Cell (f ∥ σ ▸ τ ∥ θ ▸ A ∥ {!!} ▸ B) 
  -- comp f σ τ θ A B = {!!}
