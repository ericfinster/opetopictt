{-# OPTIONS --without-K --rewriting #-}

open import Base
open import OpetopicType
open import OpetopicTypeOver

module Pi where

  -- Non-dependent Π rules

  Frm-λ : {A : Set} {B : A → Set} {n : ℕ}
    → (λf : (f : Frm A n) → Frm↓ A B f)
    → Frm (Π A B) n 

  Frm-ap : {A : Set} {B : A → Set}
    → {n : ℕ} (Πf : Frm (Π A B) n)
    → (f : Frm A n) → Frm↓ A B f

  postulate

    Cell-λ : {A : Set} {B : A → Set} {n : ℕ}
      → (λf : (f : Frm A n) → Frm↓ A B f)
      → (λτ : {f : Frm A n} (a : Cell A f) → Cell↓ A B (λf f) a)
      → Cell (Π A B) (Frm-λ λf)

    Cell-ap : {A : Set} {B : A → Set} {n : ℕ}
      → {Πf : Frm (Π A B) n} (τ : Cell (Π A B) Πf)
      → {f : Frm A n} (a : Cell A f)
      → Cell↓ A B (Frm-ap Πf f) a

  Frm-λ = {!!}
  Frm-ap = {!!}

  -- Okay, interesting.  What we're seeing then is that so far we
  -- are just making all the introduction and elimination rules
  -- compatible with the frame/tree/cell structure.  And hence they
  -- also have to commute with μ, η, γ in appropriate ways.
