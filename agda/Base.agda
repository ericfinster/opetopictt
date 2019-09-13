{-# OPTIONS --without-K --rewriting #-}

module Base where

  𝕌 = Set

  -- Rewriting
  infix 30 _↦_
  postulate  
    _↦_ : ∀ {i} {A : Set i} → A → A → Set i

  {-# BUILTIN REWRITE _↦_ #-}

  infixr 60 _,_

  record Σ (A : 𝕌) (B : A → 𝕌) : 𝕌 where
    constructor _,_
    field
      fst : A
      snd : B fst

  open Σ public

  record ⊤ : 𝕌 where
    instance constructor unit

  Unit = ⊤

  {-# BUILTIN UNIT ⊤ #-}

  data ℕ : 𝕌 where
    O : ℕ
    S : ℕ → ℕ

  {-# BUILTIN NATURAL ℕ #-}

