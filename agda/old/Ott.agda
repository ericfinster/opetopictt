{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module Ott where

  data 𝕌 : Type₁
  El : 𝕌 → Type₀

  data Frm (A : 𝕌) : Type₁
  data Frm↓ (A : 𝕌) (B : El A → Type₀) : Frm A → Type₁

  postulate
  
    Cell : {A : 𝕌} → Frm A → Type₀
    Tree : {A : 𝕌} → Frm A → Type₀

    Cell↓ : (A : 𝕌) (B : El A → Type₀) (f : Frm A) (c : Cell f) (f' : Frm↓ A B f) → Type₀
    Tree↓ : (A : 𝕌) (B : El A → Type₀) (f : Frm A) (t : Tree f) (f' : Frm↓ A B f) → Type₀

  data 𝕌 where
    𝟙 : 𝕌
    Σ' : (A : 𝕌) (B : El A → Type₀) → 𝕌

  El 𝟙 = ⊤
  El (Σ' A B) = Σ (El A) B

  data Frm (A : 𝕌) where
    ● : Frm A
    _∥_▸_ : (f : Frm A) (s : Tree f) (t : Cell f) → Frm A

  data Frm↓ (A : 𝕌) (B : El A → Type₀) where
    ■ : Frm↓ A B ●
    ext : (f : Frm A) (s : Tree f) (t : Cell f)
          (f' : Frm↓ A B f) (s' : Tree↓ A B f s f') (c' : Cell↓ A B f t f')
          → Frm↓ A B (f ∥ s ▸ t)

  
