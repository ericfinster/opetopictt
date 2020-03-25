{-# OPTIONS --without-K --rewriting --type-in-type --no-positivity #-}

open import Base

module OpetopicAgda where

  infixl 30 _∥_▸_  _∣_▸_

  data Ctx : Set where
    nil : Ctx
    cns : (A : Set) (B : A → Ctx) → Ctx

  data CtxPos : Ctx → Set where
    cns-here : (A : Set) (B : A → Ctx) → CtxPos (cns A B)
    cns-there : (A : Set) (B : A → Ctx)
      → (a : A) (p : CtxPos (B a))
      → CtxPos (cns A B)

  CtxTyp : (Γ : Ctx) (p : CtxPos Γ) → Set
  CtxTyp .(cns A B) (cns-here A B) = A
  CtxTyp .(cns A B) (cns-there A B a p) = CtxTyp (B a) p
  
  data Σ↓ : Ctx → Set where
    nil↓ : Σ↓ nil
    cns↓ : {A : Set} {B : A → Ctx}
      → (a : A) (b : Σ↓ (B a))
      → Σ↓ (cns A B)

  data Frm : Set
  data Tree : Frm → Set
  data Pos : {f : Frm} (σ : Tree f) → Set

  data Frm↓ : Frm → Set 
  data Tree↓ : {f : Frm} (f↓ : Frm↓ f) → Tree f → Set where
  data Pos↓ : {f : Frm} {f↓ : Frm↓ f} {σ : Tree f} → Tree↓ f↓ σ → Pos σ → Set where

  Cell : Frm → Set 
  Cell↓ : {f : Frm} (f↓ : Frm↓ f) (A : Cell f) → Set

  data Frm where
    ● : (Γ : Ctx) (A : Set) → Frm
    _∥_▸_ : (f : Frm) (σ : Tree f) (τ : Cell f) → Frm

  data Frm↓ where
    ∎ : {Γ : Ctx} {A : Set}
      → (g : Σ↓ Γ) (a : A)
      → Frm↓ (● Γ A)
    _∣_▸_ : {f : Frm} {σ : Tree f} {τ : Cell f}
      → (f↓ : Frm↓ f) (σ↓ : Tree↓ f↓ σ) (t : Cell↓ f↓ τ)
      → Frm↓ (f ∥ σ ▸ τ)

  record CtxCell (Γ : Ctx) (A : Set) : Set where
    field
      CtxRel : Σ↓ Γ → A → Set
      coe : Σ↓ Γ → A
      wit : (t : Σ↓ Γ) → CtxRel t (coe t)
      coh : A → Σ↓ Γ
      coh-wit : (a : A) → CtxRel (coh a) a

  open CtxCell
  
  record EqvCell (f : Frm) (σ : Tree f) (τ : Cell f) : Set where
    field
      EqvRel : {f↓ : Frm↓ f} → Tree↓ f↓ σ → Cell↓ f↓ τ → Set

  open EqvCell
  
  Cell (● Γ A) = CtxCell Γ A
  Cell (f ∥ σ ▸ τ) = EqvCell f σ τ

  Cell↓ {● Γ A} (∎ g a) C = CtxRel C g a
  Cell↓ {f ∥ σ ▸ τ} (f↓ ∣ σ↓ ▸ τ↓) C = EqvRel C σ↓ τ↓

  Typ : {f : Frm} (σ : Tree f) (p : Pos σ) → Frm
  Inh : {f : Frm} (σ : Tree f) (p : Pos σ) → Cell (Typ σ p)

  {-# TERMINATING #-}
  η : (f : Frm) (A : Cell f)
    → Tree f

  μ : (f : Frm) (σ : Tree f) 
    → (δ : (p : Pos σ) → Tree (Typ σ p))
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


  η-ctx : (A : Set) → Ctx
  η-ctx A = cns A (λ _ → nil)
  
  μ-ctx : (Γ : Ctx) 
    → (δ : (p : CtxPos Γ) → Ctx)
    → (ε : (p : CtxPos Γ) → Tree (● (δ p) (CtxTyp Γ p)))
    → Ctx

  data Tree where
    lf-ctx : (A : Set) → Tree (● (η-ctx A) A)
    nd-ctx : (Γ : Ctx) (A : Set) (C : CtxCell Γ A)
      → (δ : (p : CtxPos Γ) → Ctx)
      → (ε : (p : CtxPos Γ) → Tree (● (δ p) (CtxTyp Γ p)))
      → Tree (● (μ-ctx Γ δ ε) A)

    lf : (f : Frm) (τ : Cell f) → Tree (f ∥ η f τ ▸ τ)
    nd : (f : Frm) (σ : Tree f) (τ : Cell f) (C : EqvCell f σ τ)
       → (δ : (p : Pos σ) → Tree (Typ σ p))
       → (ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p))
       → Tree (f ∥ μ f σ δ ▸ τ)
  
  data Pos where

    nd-ctx-here : {Γ : Ctx} {A : Set} {C : CtxCell Γ A}
      → {δ : (p : CtxPos Γ) → Ctx}
      → {ε : (p : CtxPos Γ) → Tree (● (δ p) (CtxTyp Γ p))}
      → Pos (nd-ctx Γ A C δ ε)
    nd-ctx-there : {Γ : Ctx} {A : Set} {C : CtxCell Γ A}
      → {δ : (p : CtxPos Γ) → Ctx}
      → {ε : (p : CtxPos Γ) → Tree (● (δ p) (CtxTyp Γ p))}
      → (p : CtxPos Γ) (q : Pos (ε p))
      → Pos (nd-ctx Γ A C δ ε)

    nd-here : {f : Frm} {σ : Tree f} {τ : Cell f} {A : Cell (f ∥ σ ▸ τ)}
       → {δ : (p : Pos σ) → Tree (Typ σ p)}
       → {ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p)}
       → Pos (nd f σ τ A δ ε) 
    nd-there : {f : Frm} {σ : Tree f} {τ : Cell f} {A : Cell (f ∥ σ ▸ τ)}
       → {δ : (p : Pos σ) → Tree (Typ σ p)}
       → {ε : (p : Pos σ) → Tree (Typ σ p ∥ δ p ▸ Inh σ p)}
       → (p : Pos σ) (q : Pos (ε p))
       → Pos (nd f σ τ A δ ε) 

  Typ ._ (nd-ctx-here {Γ} {A}) = ● Γ A
  Typ ._ (nd-ctx-there p q) = Typ _ q
  Typ ._ (nd-here {f} {σ} {τ}) = f ∥ σ ▸ τ
  Typ ._ (nd-there p q) = Typ _ q
  
  Inh ._ (nd-ctx-here {C = C}) = C
  Inh ._ (nd-ctx-there p q) = Inh _ q
  Inh ._ (nd-here {A = A}) = A
  Inh ._ (nd-there p q) = Inh _ q

  postulate

    -- μ-ctx laws
    μ-ctx-unit-r : (Γ : Ctx)
      → μ-ctx Γ (λ p → η-ctx (CtxTyp Γ p)) (λ p → lf-ctx (CtxTyp Γ p)) ↦ Γ
    {-# REWRITE μ-ctx-unit-r #-}

    -- μ laws
    μ-unit-r : (f : Frm) (σ : Tree f) 
      → μ f σ (λ p → η (Typ σ p) (Inh σ p)) ↦ σ
    {-# REWRITE μ-unit-r #-}

  γ-ctx : (Γ : Ctx) (δ : Σ↓ Γ  → Ctx) → Ctx
  γ-ctx nil δ = δ nil↓
  γ-ctx (cns A B) δ = cns A (λ a → γ-ctx (B a) (λ b↓ → δ (cns↓ a b↓)))

  γ-lift-fst : (Γ : Ctx)
    → (δ : Σ↓ Γ  → Ctx) 
    → (s : Σ↓ (γ-ctx Γ δ))
    → Σ↓ Γ
  γ-lift-fst nil δ s = nil↓
  γ-lift-fst (cns A B) δ (cns↓ a s) =
    cns↓ a (γ-lift-fst (B a) (λ b↓ → δ (cns↓ a b↓)) s)

  γ-lift-snd : (Γ : Ctx)
    → (δ : Σ↓ Γ  → Ctx) 
    → (s : Σ↓ (γ-ctx Γ δ))
    → Σ↓ (δ (γ-lift-fst Γ δ s))
  γ-lift-snd nil δ s = s
  γ-lift-snd (cns A B) δ (cns↓ a s) =
    γ-lift-snd (B a) (λ b↓ → δ (cns↓ a b↓)) s

  transp-tree : (Γ : Ctx) (A : Set)
    → (σ : Tree (● Γ A))
    → Σ↓ Γ → A

  lift-tree : (Γ : Ctx)
    → (δ : CtxPos Γ → Ctx)
    → (ε : (p : CtxPos Γ) → Tree (● (δ p) (CtxTyp Γ p)))
    → Σ↓ (μ-ctx Γ δ ε)
    → Σ↓ Γ

  transp-tree .(cns A (λ _ → nil)) A (lf-ctx .A) (cns↓ a nil↓) = a
  transp-tree .(μ-ctx Γ δ ε) A (nd-ctx Γ .A C δ ε) s =
    coe C (lift-tree Γ δ ε s)

  -- μ-ctx : (Γ : Ctx) 
  --   → (δ : (p : CtxPos Γ) → Ctx)
  --   → (ε : (p : CtxPos Γ) → Tree (● (δ p) (CtxTyp Γ p)))
  --   → Ctx
  μ-ctx nil δ ε = nil
  μ-ctx (cns A B) δ ε = 
    let Γ' = δ (cns-here A B)
        a s = transp-tree Γ' A (ε (cns-here A B)) s
        δ' s t = δ (cns-there A B (a s) t)
        ε' s t = ε (cns-there A B (a s) t)
        ϕ s = μ-ctx (B (a s)) (δ' s) (ε' s)
    in γ-ctx Γ' ϕ

  lift-tree nil δ ε s = s
  lift-tree (cns A B) δ ε s = 
    let Γ' = δ (cns-here A B)
        a s = transp-tree Γ' A (ε (cns-here A B)) s
        δ' s t = δ (cns-there A B (a s) t)
        ε' s t = ε (cns-there A B (a s) t)
        ϕ s = μ-ctx (B (a s)) (δ' s) (ε' s)
        s' = γ-lift-fst Γ' ϕ s
    in cns↓ (a s') (lift-tree (B (a s')) (δ' s') (ε' s') (γ-lift-snd Γ' ϕ s))

  -- η : (f : Frm) (A : Cell f)
  --   → Tree f
  η (● Γ A) C =
    let η-ctx-dec p = η-ctx (CtxTyp Γ p)
        lf-ctx-dec p = lf-ctx (CtxTyp Γ p)
     in nd-ctx Γ A C η-ctx-dec lf-ctx-dec
  η (f ∥ σ ▸ τ) C = 
    let η-dec p = η (Typ σ p) (Inh σ p)
        lf-dec p = lf (Typ σ p) (Inh σ p)
    in nd f σ τ C η-dec lf-dec

  μ = {!!}

  

  --
  --  A sketch of how to now define 𝕌-opetopic types ...
  --

  Poly : Set → Set
  Poly I = (A : Set) → I → (A → I) → Set

  _×_ : {I : Set} → Poly I → Poly I → Poly I
  (P × Q) A i ϕ = Σ (P A i ϕ) (λ _ → Q A i ϕ)

  record BiPolySeq (I : Set) : Set where
    coinductive
    field
      P : Poly I
      Q : Poly I
      Next : BiPolySeq (Σ Set (λ A → Σ I (λ i → Σ (A → I) (λ ϕ → (P × Q) A i ϕ))))

  -- But maybe we don't need the whole polynomial structure here?

  record BiGlobSet (I : Set) : Set where
    coinductive
    field
      Src : I → Set
      Tgt : I → Set
      Plc : (i : I) → Src i → Set
      Clr : (i : I) (s : Src i) (p : Plc i s) → I
      Ocp : (i : I) (s : Src i) (p : Plc i s) → Tgt (Clr i s p)
      Then : BiGlobSet (Σ I (λ i → Σ (Src i) (λ s → Tgt i)))

  open BiGlobSet

  Up : {I : Set} (B : BiGlobSet I) (X : I → Set) → BiGlobSet (Σ I X)
  Src (Up B X) (i , x) = Σ (Src B i) (λ s → (p : Plc B i s) → X (Clr B i s p))
  Tgt (Up B X) (i , x) = Tgt B i
  Plc (Up B X) (i , x) (s , ϕ) = Plc B i s
  Clr (Up B X) (i , x) (s , ϕ) p = (Clr B i s p , ϕ p)
  Ocp (Up B X) (i , x) (s , ϕ) p = Ocp B i s p
  Then (Up B X) =
    let X' = λ { (i , s , t) → Σ (X i) (λ _ → (p : Plc B i s) → X (Clr B i s p)) }
        res = Up (Then B) X'
    in {!res!}

  record BiOpTyp {I : Set} (B : BiGlobSet I) : Set where
    coinductive
    field
      X : (i : I) → Set
      TheRest : BiOpTyp (Then (Up B X))
      
  -- So we certainly have one of these with the universe.  But I think we have
  -- just a little bit more: there is a canonical fibration on A and every one
  -- of those guys gives a B.  And so, we should be able to make sense of a
  -- kind of "extension" of this guy.


  _↑_ : {I : Set} (P : Poly I) (X : I → Set) → Poly (Σ I X)
  (P ↑ X) A (i , x) ϕ = P A i (λ a → fst (ϕ a))
  
  record PolySeq (I : Set) : Set where
    coinductive
    field
      P : Poly I
      H : PolySeq (Σ Set (λ A → Σ I (λ i → Σ (A → I) (λ ϕ → P A i ϕ)))) 

  open PolySeq
  
  _⇑_ : {I : Set} (Q : PolySeq I) (X : I → Set) → PolySeq (Σ I X)
  P (_⇑_ {I} Q X) = (P Q) ↑ X
  H (_⇑_ {I} Q X ) = {!ch!}
    -- Have to "transport" along the canonical equiv here ...
    -- Could there be a clever way to avoid this?
  
      where X' : Σ Set (λ A → Σ I (λ i → Σ (A → I) (P Q A i))) → Set
            X' (A , i , ϕ , _) = Σ (X i) (λ _ → (a : A) → X (ϕ a))
            
            ch = (H Q) ⇑ X'

  record PType {I : Set} (P : PolySeq I) : Set where
    coinductive
    field

      Here : I → Set
      There : PType (H (P ⇑ Here))

  -- Now a 𝕌-opetopic type will be a PType for the above
  -- constructed sequence of polynomials....

  -- Ahh! This won't work!  Because in the sequence of "polynomials"
  -- you have in mind for the universe, the index does not change by
  -- summing the constructors each time.  Rather, it sums the
  -- constructors *and* the trees.

  -- This kind of reveals a bit more what you are up to here: instead
  -- of using the usual Baez-Dolan construction, you immediately sum
  -- over constructors and trees so that the operations of the next
  -- polynomial *really are* just the relations.  What this
  -- accomplishes is that tree substitution is no longer part of the
  -- monad multiplication, which is why it makes sense to now force
  -- it to have good definitional properties.  I see.

  -- But this means we have to revisit the definition above (which
  -- I didn't much care for anyway....)

  -- Okay, maybe we can use this idea of "boundaries" or "products
  -- of polynomials" to have a sequence....  Right.  Because that's
  -- really what's happening
