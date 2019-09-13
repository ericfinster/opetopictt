{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import OpetopicTypes

module Fibration where

  has-refl : (A : 𝕆) → Type₀
  has-refl A = {n : ℕ} (f : Frm A n) (c : Cell A f) → Cell A (f ∥ η f c ▸ c)

  has-J : (A : 𝕆) (refl : has-refl A) → Type₁
  has-J A refl = {n : ℕ} (f : Frm A n)
                 (P : (c d : Cell A f) → Cell A (f ∥ η f c ▸ d) → Type₀)
                 (j : (c : Cell A f) → P c c (refl f c))
                 (c d : Cell A f) (p : Cell A (f ∥ η f c ▸ d)) → P c d p

  module _ (A : 𝕆) (refl : has-refl A) (J : has-J A refl) where

    has-comps : {n : ℕ} (f : Frm A n) (σ : Tree A f) → Cell A f
    has-comps .● (ob α) = α
    has-comps .(f ∥ η f α ▸ α) (lf f α) = refl f α
    has-comps .(f ∥ μ f σ δ ▸ τ) (nd f σ τ α δ ε) =
      let ε' p = has-comps _ (ε p)
      in {!!}
