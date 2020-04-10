{-# OPTIONS --without-K --rewriting #-}

open import Base
open import Opetopes
open import OpetopicType
open import OpetopicTypeOver
open import Cell

module CellCellOver where

  -- Cells in a Cell↓ are cells over degeneracies.

  -- So, we need to degenerate τ according to the shape of fc.  Then
  -- we will recursively extend f↓ using the inducion hypothesis.
  -- Finally, the "top-level" degeneracy of τ will be the cell that we
  -- are supposed to live over.

  -- In order for this to work, we need to be able to degenerate an
  -- arbitrary cell.  I *believe* this is already possibly using the
  -- relation that cells in cells are extended cells.

  -- So let's try to do this.

  degen-frm : {A : Set}
    → {n m : ℕ} {o : 𝕆 n}
    → {f : Frm A o} (τ : Cell A f)
    → (od : 𝕆 m)
    → Frm A (o ⊕ od)
    
  degen-cell : {A : Set}
    → {n m : ℕ} {o : 𝕆 n} 
    → {f : Frm A o} (τ : Cell A f)
    → (od : 𝕆 m) → Cell A (degen-frm τ od)

  degen-tr : {A : Set}
    → {n m : ℕ} {o : 𝕆 n} 
    → {f : Frm A o} (τ : Cell A f)
    → (od : 𝕆 m) (td : 𝕋 (o ⊕ od))
    → Tree A (degen-frm τ od) td

  degen-frm {f = f} τ ○ = f ∥ η f τ ▹ τ
  degen-frm {A = A} {o = o} τ (od ∣ t) = degen-frm τ od ∥
    degen-tr τ od (o ⊕t t) ▹ degen-cell {A = A} τ od
  
  degen-cell τ ○ = Cell-refl τ ○
  degen-cell τ (od ∣ t) = {!!}
  
  degen-tr = {!!}

  -- postulate

  --   Cell-Cell↓ : {A : Set} {B : A → Set}
  --     → {n m : ℕ} {o : 𝕆 n} {oc : 𝕆 m}
  --     → {f : Frm A o} (τ : Cell A f)
  --     → {f↓ : Frm↓ A B f}
  --     → (fc : Frm (Cell↓ A B f↓ τ) oc)
  --     → Cell (Cell↓ A B f↓ τ) fc ↦ Cell↓ A B {!!} {!!}
