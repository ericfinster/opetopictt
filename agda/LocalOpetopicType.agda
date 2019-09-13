{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module LocalOpetopicType where

  postulate

    𝕆 : Type₀

  data Frm (A : 𝕆) (Γ : Type₀) : Type₀
  data Tree (A : 𝕆) : (Γ : Type₀) (f : Frm A Γ) → Type₀

  -- postulate

  --   Cell : (A : 𝕆) (f : Frm A) → Type₀

  data Frm (A : 𝕆) (Γ : Type₀) where
    ● : Frm A Γ

  data Tree (A : 𝕆) where



