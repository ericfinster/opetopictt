{-# OPTIONS --without-K --rewriting --type-in-type --no-positivity #-}

open import Base

module Universe where

  data Frm : Set
  data Cell : Frm → Set
  data Tree : Frm → Set
  data Nd : {f : Frm} → Tree f → Set

  data TmFrm : Frm → Set
  data TmTree : {f : Frm} → TmFrm f → Tree f → Set

  El : {f : Frm} (α : Cell f) (ftm : TmFrm f) → Set

  infixl 30 _∥_▸_
  
  data Frm where
    ● : Frm 
    _∥_▸_ : (f : Frm) (σ : Tree f) (τ : Cell f) → Frm

  data TmFrm where
    ∎ : TmFrm ● 
    ext : {f : Frm} {σ : Tree f} {τ : Cell f}
      → (ftm : TmFrm f) (σtm : TmTree ftm σ) (τtm : El τ ftm)
      → TmFrm (f ∥ σ ▸ τ)

  Typ : {f : Frm} (σ : Tree f) (p : Nd σ) → Frm 
  Inh : {f : Frm} (σ : Tree f) (p : Nd σ) → Cell (Typ σ p)

  η : {f : Frm} → Cell f → Tree f
  
  μ : {f : Frm} (σ : Tree f)
    → (κ : (p : Nd σ) → Tree (Typ σ p))
    → Tree f

  data Cell where
    Σ' : {f : Frm} (σ : Tree f) → Cell f
    -- Then there should be a "witness" for this guy ...

  
  data Tree where
    nil : Tree ●
    cns : (α : Cell ●) (β : (a : El α ∎) → Tree ●) → Tree ●
    
    lf : (f : Frm) (α : Cell f) → Tree (f ∥ η α ▸ α)
    nd : (f : Frm) (σ : Tree f) (τ : Cell f) (α : Cell (f ∥ σ ▸ τ))
       → (δ : (p : Nd σ) → Tree (Typ σ p))
       → (ε : (p : Nd σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
       → Tree (f ∥ μ σ δ ▸ τ)

  data Nd where
    cns-here : (α : Cell ●) (β : (a : El α ∎) → Tree ●)
             → Nd (cns α β)
    cns-there : (α : Cell ●) (β : (a : El α ∎) → Tree ●)
              → (a : El α ∎) (n : Nd (β a))
              → Nd (cns α β)

    -- Here also, should I pick up an element of the cell?
    nd-here : (f : Frm) (σ : Tree f) (τ : Cell f) (α : Cell (f ∥ σ ▸ τ))
            → (δ : (p : Nd σ) → Tree (Typ σ p))
            → (ε : (p : Nd σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
            → Nd (nd f σ τ α δ ε)
    nd-there : (f : Frm) (σ : Tree f) (τ : Cell f) (α : Cell (f ∥ σ ▸ τ))
             → (δ : (p : Nd σ) → Tree (Typ σ p))
             → (ε : (p : Nd σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
             → (e : El α {!!}) (p : Nd σ) (n : Nd (ε p)) 
             → Nd (nd f σ τ α δ ε)


  data TmTree where

  El {f} (Σ' σ) ftm = TmTree ftm σ

  Typ = {!!}
  Inh = {!!}
  
  η {●} α = cns α (λ _ → nil)
  η {f ∥ σ ▸ τ} α = {!!}
  
  μ = {!!}
  
  -- Typ {●} (ob α) _ = ●
  -- Typ {f ∥ .(η τ) ▸ τ} (lf .f .τ) ()
  -- Typ {f ∥ .(μ σ δ) ▸ τ} (nd .f σ .τ α δ ε) (nd-here .f .σ .τ .α .δ .ε) = f ∥ σ ▸ τ
  -- Typ {f ∥ .(μ σ δ) ▸ τ} (nd .f σ .τ α δ ε) (nd-there .f .σ .τ .α .δ .ε e p q) = Typ (ε p) q

  -- Inh {●} (ob α) _ = α
  -- Inh {f ∥ .(η τ) ▸ τ} (lf .f .τ) ()
  -- Inh {f ∥ .(μ σ δ) ▸ τ} (nd .f σ .τ α δ ε) (nd-here .f .σ .τ .α .δ .ε) = α
  -- Inh {f ∥ .(μ σ δ) ▸ τ} (nd .f σ .τ α δ ε) (nd-there .f .σ .τ .α .δ .ε e p q) = Inh (ε p) q

  -- η {●} α = ob α
  -- η {f ∥ σ ▸ τ} α = {!nd f σ τ α ? ?!}

  -- -- η (f ∥ σ ▸ τ) α =  
  -- --   let η-dec p = η (Typ f σ p) (Inh f σ p)
  -- --       lf-dec p = lf (Typ f σ p) (Inh f σ p)
  -- --   in nd f σ τ α η-dec lf-dec

  -- μ {●} (ob α) κ = {!!}
  -- μ {f ∥ σ ▸ τ} σ' κ = {!!}


  -- Not sure we need this anymore ...
  -- data Lf : {f : Frm} → Tree f → Set  

  -- data Lf where
  --   lf-nil : Lf nil
  --   lf-cns : (α : Cell ●) (β : (a : El α {!!}) → Tree ●)
  --          → (a : El α {!!}) (l : Lf (β a))
  --          → Lf (cns α β)
           
  --   -- Should this take an element of the cell?
  --   lf-lf : (f : Frm) (α : Cell f) → Lf (lf f α)
  --   lf-nd : (f : Frm) (σ : Tree f) (τ : Cell f) (α : Cell (f ∥ σ ▸ τ))
  --         → (δ : (p : Nd σ) → Tree (Typ σ p))
  --         → (ε : (p : Nd σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
  --         → (e : El α {!!}) (p : Nd σ) (l : Lf (ε p)) 
  --         → Lf (nd f σ τ α δ ε)
