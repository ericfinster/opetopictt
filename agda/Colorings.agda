{-# OPTIONS --without-K --rewriting #-}

open import Base
open import Opetopes

module Colorings where

  -- Yeah, it's messy, but this looks like a solution.
  data InnerFace : {n : ℕ} → 𝕆 n → ℕ → 𝕌 where
    src-face : {n : ℕ} (o : 𝕆 n) (p : ℙ o) (q : ℙ (o ▸ p)) (u : Pos q) → InnerFace (o ▸ p ▸ q) (S n)
    tgt-face : {n : ℕ} (o : 𝕆 n) (p : ℙ o) (q : ℙ (o ▸ p)) (u : Pos q) → InnerFace (o ▸ p ▸ q) n
    raise-face : {n m : ℕ} (o : 𝕆 n) (p : ℙ o) → InnerFace o m → InnerFace (o ▸ p) m

  data Face : {n : ℕ} → 𝕆 n → ℕ → 𝕌 where
    top : {n : ℕ} (o : 𝕆 n) → Face o n
    tgt : {n : ℕ} (o : 𝕆 (S n)) → Face o n
    init : {n : ℕ} (o : 𝕆 (S n)) → Face o 0
    inner : {n m : ℕ} (o : 𝕆 n) → InnerFace o m → Face o m
    
  ob-face : Face ● 0
  ob-face = top ●

  arr-src-face : Face arrow 0
  arr-src-face = init (● ▸ arr)

  arr-tgt-face : Face arrow 0
  arr-tgt-face = tgt (● ▸ arr)

  drop-obj-face : Face 2-drop 0
  drop-obj-face = init _

  drop-arr-face : Face 2-drop 1
  drop-arr-face = tgt _

  simplex-obj-face : Face 2-simplex 0
  simplex-obj-face = inner _ (tgt-face ● arr _ (nd-pos-here ● arr _ _))

  -- Here's a kind of first draft.  But probably you will have
  -- to have some kind of restrictions based on the ordering
  -- of ℕ ....

  -- m < n
  
  data Coloring : {n m : ℕ} (o : 𝕆 n) (p : 𝕆 m) → 𝕌 where
    base : Coloring ● ●
    less : {n : ℕ} {m : ℕ} (oₛ : 𝕆 n) (oₜ : 𝕆 m) (pₜ : ℙ oₜ)
      → Coloring oₛ oₜ → Coloring oₛ (oₜ ▸ pₜ)
    more : {n : ℕ} {m : ℕ} (oₛ : 𝕆 n) (pₛ : ℙ oₛ) (oₜ : 𝕆 m)
      → (c : Coloring oₛ oₜ)  -- Need this?
      → (π : (u : Pos pₛ) → Coloring (Typ pₛ u) oₜ)
      → Coloring (oₛ ▸ pₛ) oₜ
    same : {n : ℕ} (oₛ : 𝕆 n) (oₜ : 𝕆 n) (pₛ : ℙ oₛ) (pₜ : ℙ oₜ)
      → (c : Coloring oₛ oₜ) -- Need this?
      → (π : (u : Pos pₛ) → Σ (Pos pₜ) (λ v → Coloring (Typ pₛ u) (Typ pₜ v)))
      → Coloring (oₛ ▸ pₛ) (oₜ ▸ pₜ)

