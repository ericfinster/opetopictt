{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import OpetopicTypes

module Examples where

  module _ {A : 𝕆} where

    Ob : Type₀
    Ob = Cell A ● 

    Arr : (s : Ob) (t : Ob) → Type₀
    Arr s t = Cell A (● ∥ ob s ▸ t)
    
    ArrSeq : (s : Ob) (t : Ob) → Type₀
    ArrSeq s t = Tree A (● ∥ ob s ▸ t)

    arrTr : (s : Ob) (t : Ob) (f : Arr s t) → ArrSeq s t
    arrTr s t f = nd (ob s) t f (λ p → ob (Inh (ob s) p)) (λ p → lf ● s)

    SeqComp : {s t u : Ob} (f : ArrSeq s t) (g : ArrSeq t u) → ArrSeq s u
    SeqComp {s} {t} {u} f g = γ (ob t) u g (λ p → ob s) (λ p → f)

    muString : {n : ℕ} {f : Frm A n} (σ : Tree A f)
      → (κ₀ : (p : Pos σ) → Tree A (Typ σ p))
      → (κ₁ : (p : Pos σ) (q : Pos (κ₀ p)) → Tree A (Typ (κ₀ p) q))
      → Tree A f
    muString σ κ₀ κ₁ = μ σ (λ p → μ (κ₀ p) (λ q → μ (κ₁ p q) (λ r → η (Inh (κ₁ p q) r))))

    -- I wanted to know if it is possible to have a neutral tree
    -- but with a decoration which was not stuck on an η.  The
    -- following example suggest that this is not possible....
    -- Can we think of a proof?
    -- badMu : {n : ℕ} {f : Frm A n}
    --   → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
    --   → Tree A (f ∥ σ ▸ τ)
    -- badMu σ τ ρ = μ ρ (λ p → {!!})

    -- Ah, interesting. So no, the type gets completely abstracted
    -- and we don't see that it is itself a composite of something.
    -- Okay, so maybe this saves us....

    -- I think this example shows that we need gamma as a primitive.  
    gammaTest : {n : ℕ} {f : Frm A n}
      → (σ : Tree A f) (τ : Cell A f) (α : Cell A (f ∥ σ ▸ τ))
      → (δ : (p : Pos σ) → Tree A (Typ σ p))
      → (ε : (p : Pos σ) → Tree A (Typ σ p ∥ δ p ▸ Inh σ p))
      → (κ : (p : Pos (nd σ τ α δ ε)) → Tree A (Typ (nd σ τ α δ ε) p))
      → Tree A (f ∥ μ σ δ ▸ τ)
    gammaTest σ τ α δ ε κ =  μ (nd σ τ α δ ε) κ 
    
  postulate

    Typ' : {A : 𝕆} {n : ℕ} {f : Frm A n}
      → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
      → (p : Pos σ) → Frm A n

