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

  postulate

    Typ' : {A : 𝕆} {n : ℕ} {f : Frm A n}
      → (σ : Tree A f) (τ : Cell A f) (ρ : Tree A (f ∥ σ ▸ τ))
      → (p : Pos σ) → Frm A n

