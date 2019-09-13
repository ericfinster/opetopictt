{-# OPTIONS --without-K --rewriting #-}

open import OpetopicTypes

module Equality where

  _==_ : {A : 𝕌} → A → A → 𝕌
  _==_ {A} a b = Cell A (● ∥ ob a ▸ b)

  idp : {A : 𝕌} → (a : A) → a == a
  idp a = comp (● ∥ ob a ▸ a) (lf ● a)

  _∙_ : {A : 𝕌} {a b c : A}
    → (p : a == b) (q : b == c)
    → a == c
  _∙_ {A} {a} {b} {c} p q =
    comp (● ∥ ob a ▸ c)
         (nd ● (ob b) c q
             (ob-pos-elim b (λ _ →  (Tree A ●)) (ob a))
             (ob-pos-elim b (λ p → Tree A (● ∥ ob-pos-elim b (λ _ → Tree A ●) (ob a) p ▸ b))
                            (η (● ∥ ob a ▸ b) p)))

  postulate

    -- This is the generic case, but it appears
    -- we have to give the two cases separately
    -- in order to recognize the rewrite ...
    
    -- comp-η : {A : 𝕌} (f : Frm A) (α : Cell A f)
    --   → comp f (η f α) ↦ α
    -- {-# REWRITE comp-η #-}

    -- fill-η : {A : 𝕌} (f : Frm A) (α : Cell A f)
    --   → fill f (η f α) ↦ comp (f ∥ η f α ▸ α) (lf f α)
    -- {-# REWRITE fill-η #-}

    comp-●-η : {A : 𝕌} (a : A)
      → comp ● (ob a) ↦ a
    {-# REWRITE comp-●-η #-}

    fill-●-η : {A : 𝕌} (a : A)
      → fill ● (ob a) ↦ idp a
    {-# REWRITE fill-●-η #-}

  -- If compositions are strict on units, then we can
  -- prove Martin-Lof's J rule.  Is this problematic?
  
  MLJ : {A : 𝕌} {a : A}
    → (P : (b : A) → a == b → 𝕌)
    → (d : P a (idp a))
    → (b : A) (p : a == b) → P b p
  MLJ {A} {a} P d b p = J ● (ob a) P d b p



