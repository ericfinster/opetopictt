{-# OPTIONS --without-K --rewriting #-}

open import Base
open import OpetopicType
open import OpetopicTypeOver

module Kan where

  --
  --  First possibility: define contractibility and state that
  --  the space of fillers is contractible.
  --
  
  is-contr-by-filling : (A : Set) → Set
  is-contr-by-filling A = {n : ℕ} (f : Frm A n) → Cell A f

  contractible-filling-spaces : Set₁
  contractible-filling-spaces = 
    (A : Set) {n : ℕ} (f : Frm A n) (σ : Tree A f)
      → is-contr-by-filling (Σ (Cell A f) (λ τ → Cell A (f ∣ σ ▸ τ)))

  --
  --  Second possibility: source and target universality.  This
  --  is a special case of the Kan condition, but one which I
  --  think should be equivalent.
  --

  postulate

    -- Again, these should be stated for the *dependent* version,
    -- since what we care about is the fibrational property

    -- There's still a kind of asymmetry in the definition of the
    -- source fillers.  Why not return a decoration of trees? Or
    -- why not allow θ to be a tree, and use γ to tack on the
    -- results?

    source-universal-lifts : {A : Set} {n : ℕ} {f : Frm A n}
      → (σ : Tree A f) (τ : Cell A f) (θ : Cell A (f ∣ σ ▸ τ))
      → (δ : (p : Pos σ) → Tree A (Typ σ p))
      → (ζ : Cell A (f ∣ μ σ δ ▸ τ))
      → (p : Pos σ) → Cell A (Typ σ p ∣ δ p ▸ Inh σ p) 

    source-universal-fill : {A : Set} {n : ℕ} {f : Frm A n}
      → (σ : Tree A f) (τ : Cell A f) (θ : Cell A (f ∣ σ ▸ τ))
      → (δ : (p : Pos σ) → Tree A (Typ σ p))
      → (ζ : Cell A (f ∣ μ σ δ ▸ τ))
      → Cell A (f ∣ μ σ δ ▸ τ ∣ nd f σ τ θ δ (λ p → η (Typ σ p ∣ δ p ▸ Inh σ p) (source-universal-lifts σ τ θ δ ζ p)) ▸ ζ)

    target-universal-lift : {A : Set} {n : ℕ} {f : Frm A n}
      → (σ : Tree A f) (τ : Cell A f) 
      → (δ : (p : Pos σ) → Tree A (Typ σ p))
      → (ε : (p : Pos σ) → Tree A (Typ σ p ∣ δ p ▸ Inh σ p))
      → (ζ : Cell A (f ∣ μ σ δ ▸ τ))
      → Cell A (f ∣ σ ▸ τ)

    target-universal-fill : {A : Set} {n : ℕ} {f : Frm A n}
      → (σ : Tree A f) (τ : Cell A f) 
      → (δ : (p : Pos σ) → Tree A (Typ σ p))
      → (ε : (p : Pos σ) → Tree A (Typ σ p ∣ δ p ▸ Inh σ p))
      → (ζ : Cell A (f ∣ μ σ δ ▸ τ))
      → Cell A (f ∣ μ σ δ ▸ τ ∣ nd f σ τ (target-universal-lift σ τ δ ε ζ) δ ε ▸ ζ)


  --
  --  Remarks:
  --
  --  1) I'm not sure if this simultaneous filling on the source
  --     positions actually buys you anything.  When you come to
  --     constructing fillings for say Π or 𝕌, I think you will still
  --     need to quantify over all positions not equal to a given one.
  --     So maybe you should just say it that way.
  --
  --  2) There actually probably is a way to get all Kan fillers
  --     directly: You have a tree.  Then at some position you have a
  --     tree of the right kind and a higher decoration of its source.
  --     Then you get the missing cell.  Just don't know if the typing
  --     will work out definitionally or not.
  -- 
  --  3) Basically, it will really just depend on what you can actually
  --     construct when it comes to the type constructors.
  --
  --  4) One way to not have to depend on the decidable equality of
  --     positions would be to have some partial substitution
  --     operations, modifying the tree at a single position.  But
  --     then you would need to axiomatize the fact that they commute,
  --     and this isn't completely clear.
  -- 
