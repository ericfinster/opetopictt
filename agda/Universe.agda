{-# OPTIONS --without-K --rewriting --type-in-type --no-positivity #-}

open import Base

module Universe where

  infixl 30 _∥_▸_

  data 𝕌 : Set where

  El : 𝕌 → Set
  El = {!!}
  
  data Frm : 𝕌 → Set
  data Tree : {Γ : 𝕌} → Frm Γ → Set
  data Pos : {Γ : 𝕌} {f : Frm Γ} → Tree f → Set
  data Cell : {Γ : 𝕌} → Frm Γ → Set

  data Frm where
    ●_ : (Γ : 𝕌) → Frm Γ
    _∥_▸_ : {Γ : 𝕌} (f : Frm Γ) (σ : Tree f) (τ : Cell f) → Frm Γ

  data Tree where
    tr : {Γ : 𝕌} → Tree (● Γ)

  data Pos where
    

  data Cell where
    ob : {Γ : 𝕌} → Cell (● Γ) 
    ext : {Γ : 𝕌} (A : El Γ → 𝕌) → Cell ((● Γ) ∥ tr ▸ ob)

  Ctx : {Γ : 𝕌} {f : Frm Γ} (σ : Tree f) (p : Pos σ) → 𝕌
  Typ : {Γ : 𝕌} {f : Frm Γ} (σ : Tree f) (p : Pos σ) → Frm (Ctx σ p) 
  Inh : {Γ : 𝕌} {f : Frm Γ} (σ : Tree f) (p : Pos σ) → Cell (Typ σ p)

  Ctx {Γ} {f} σ p = {!!}
  
  Typ = {!!}
  Inh = {!!}
