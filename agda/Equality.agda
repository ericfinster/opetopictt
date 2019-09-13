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

