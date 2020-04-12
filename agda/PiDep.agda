{-# OPTIONS --without-K --rewriting #-}

open import Base
open import Opetopes
open import OpetopicType
open import OpetopicTypeOver
open import Sigma
open import Pi

module PiDep where

  -- Dependent Π
  
  Π↑ : {Γ : Set} (A : Γ → Set) (B : Σ Γ A → Set) → Γ → Set
  Π↑ A B γ = Π (A γ) (λ a → B (γ , a))

  Frm-ev↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
    → {n : ℕ} {o : 𝕆 n} {γ : Frm Γ o}
    → (π₀ : Frm↓ Γ (Π↑ A B) γ)
    → (a₀ : Frm↓ Γ A γ)
    → Frm↓ (Σ Γ A) B (Frm-pr γ a₀)

  Tree-ev↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
    → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
    → {γ₀ : Frm Γ o} {γ : Tree Γ γ₀ t}
    → {π₀ : Frm↓ Γ (Π↑ A B) γ₀} (π : Tree↓ Γ (Π↑ A B) π₀ γ)
    → {a₀ : Frm↓ Γ A γ₀} (a : Tree↓ Γ A a₀ γ)
    → Tree↓ (Σ Γ A) B (Frm-ev↓ π₀ a₀) (Tree-pr γ a)

  postulate

    Cell-λ↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {o : 𝕆 n} {γ₀ : Frm Γ o} {γ : Cell Γ γ₀}
      → {π₀ : Frm↓ Γ (Π↑ A B) γ₀ }
      → ((a₀ : Frm↓ Γ A γ₀) (a : Cell↓ Γ A a₀ γ) → Cell↓ (Σ Γ A) B (Frm-ev↓ π₀ a₀) (γ , a))
      → Cell↓ Γ (Π↑ A B) π₀ γ    

    Cell-ev↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {o : 𝕆 n} {γ₀ : Frm Γ o} {γ : Cell Γ γ₀}
      → {π₀↓ : Frm↓ Γ (Π↑ A B) γ₀}
      → (τ↓ : Cell↓ Γ (Π↑ A B) π₀↓ γ)
      → {a₀↓ : Frm↓ Γ A γ₀} (aτ↓ :  Cell↓ Γ A a₀↓ γ)
      → Cell↓ (Σ Γ A) B (Frm-ev↓ π₀↓ a₀↓) (γ , aτ↓)

    Cell-λ↓-ev↓  : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {o : 𝕆 n} {f : Frm Γ o} {τ : Cell Γ f}
      → (f↓ : Frm↓ Γ (Π↑ A B) f)
      → (τ↓ : Cell↓ Γ (Π↑ A B) f↓ τ)
      → Cell-λ↓ (λ f₁ τ₁ → Cell-ev↓ τ↓ τ₁) ↦ τ↓
    {-# REWRITE Cell-λ↓-ev↓  #-}

    Tree-ev-typ↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm Γ o} (σ : Tree Γ f t)
      → {f↓ : Frm↓ Γ (Π↑ A B) f} → (σ↓ : Tree↓ Γ (Π↑ A B) f↓ σ)
      → {af↓ : Frm↓ Γ A f} (aσ↓ : Tree↓ Γ A af↓ σ)
      → (p : Pos t)
      → Typ↓ (Tree-ev↓ σ↓ aσ↓) p ↦ Frm-ev↓ (Typ↓ σ↓ p) (Typ↓ aσ↓ p)
    {-# REWRITE Tree-ev-typ↓ #-}

    Tree-ev-inh↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {f : Frm Γ o} (σ : Tree Γ f t)
      → {f↓ : Frm↓ Γ (Π↑ A B) f} (σ↓ : Tree↓ Γ (Π↑ A B) f↓ σ)
      → {af↓ : Frm↓ Γ A f} (aσ↓ : Tree↓ Γ A af↓ σ)
      → (p : Pos t)
      → Inh↓ (Tree-ev↓ σ↓ aσ↓) p ↦ Cell-ev↓ (Inh↓ σ↓ p) (Inh↓ aσ↓ p)
    {-# REWRITE Tree-ev-inh↓ #-}

    Tree-ev-η↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {o : 𝕆 n} 
      → {f : Frm Γ o} (τ : Cell Γ f)
      → {f↓ : Frm↓ Γ (Π↑ A B) f} (τ↓ : Cell↓ Γ (Π↑ A B) f↓ τ)
      → {af↓ : Frm↓ Γ A f} (aτ↓ : Cell↓ Γ A af↓ τ)
      → Tree-ev↓ (η↓ f↓ τ↓)(η↓ af↓ aτ↓) ↦ η↓ (Frm-ev↓ f↓ af↓) (Cell-ev↓ τ↓ aτ↓) 
    {-# REWRITE Tree-ev-η↓ #-}

    Tree-ev-μ↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → {n : ℕ} {o : 𝕆 n} {t : 𝕋 o}
      → {δₒ : (p : Pos t) → 𝕋 (Typₒ t p)}
      → {f : Frm Γ o} (σ : Tree Γ f t)
      → (δ : (p : Pos t) → Tree Γ (Typ σ p) (δₒ p))
      → {f↓ : Frm↓ Γ (Π↑ A B) f} (σ↓ : Tree↓ Γ (Π↑ A B) f↓ σ)
      → (δ↓ : (p : Pos t) → Tree↓ Γ (Π↑ A B) (Typ↓ σ↓ p) (δ p))
      → {af↓ : Frm↓ Γ A f} (aσ↓ : Tree↓ Γ A af↓ σ)
      → (aδ↓ : (p : Pos t) → Tree↓ Γ A (Typ↓ aσ↓ p) (δ p))
      → Tree-ev↓ (μ↓ σ↓ δ↓) (μ↓ aσ↓ aδ↓) ↦ μ↓ (Tree-ev↓ σ↓ aσ↓) (λ p → Tree-ev↓ (δ↓ p) (aδ↓ p))
    {-# REWRITE Tree-ev-μ↓ #-}

  Frm-ev↓ (■ s₀ ▸ s₁) (■ a₀ ▸ a₁) = ■ s₀ a₀ ▸ s₁ a₁
  Frm-ev↓ (f ∥ σ ▸ τ) (af ∥ aσ ▸ aτ) = Frm-ev↓ f af ∥ Tree-ev↓ σ aσ ▸ Cell-ev↓ τ aτ

  Tree-ev↓ (nil↓ s) (nil↓ a) = nil↓ (s a)
  Tree-ev↓ (cns↓ sρ sσ) (cns↓ aρ aσ) = cns↓ (Cell-ev↓ sρ aρ) (Tree-ev↓ sσ aσ)
  Tree-ev↓ (lf↓ sf sτ) (lf↓ af aτ) = lf↓ (Frm-ev↓ sf af) (Cell-ev↓ sτ aτ)
  Tree-ev↓ (nd↓ sσ sτ sθ sδ sε) (nd↓ {f↓ = af} aσ aτ aθ aδ aε) =
    nd↓ (Tree-ev↓ sσ aσ) (Cell-ev↓ sτ aτ) (Cell-ev↓ sθ aθ)
        (λ p → Tree-ev↓ (sδ p) (aδ p))
        (λ p → Tree-ev↓ (sε p) (aε p))

{-
  -- Low dimensional rewrites
  postulate

    Cell-ap↓-● : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
      → (γ : Cell Γ ●) (π : Cell↓ Γ (Π↑ A B) ■ γ) (a : Cell↓ Γ A ■ γ)
      → Cell-ap↓ {γ₀ = ●} {π₀ = ■} π a ↦ ⟦ B ∣ ⟦ Π↑ A B ∣ π ⟧↓ ⟦ A ∣ a ⟧↓ ⟧↑
    {-# REWRITE Cell-ap↓-● #-}

  --
  --  Compositions for Pi
  --

  has-comps : {A : Set} (B : A → Set) → Set
  has-comps {A} B =
      {n : ℕ} {f : Frm A n}
    → {σ : Tree A f} {τ : Cell A f} (θ : Cell A (f ∣ σ ▸ τ))
    → {f↓ : Frm↓ A B f} (σ↓ : Tree↓ A B f↓ σ)
    → Cell↓ A B f↓ τ

  has-fills : {A : Set} (B : A → Set) (hc : has-comps B) → Set
  has-fills {A} B hc =
      {n : ℕ} {f : Frm A n}
    → (σ : Tree A f) (τ : Cell A f) (θ : Cell A (f ∣ σ ▸ τ))
    → (f↓ : Frm↓ A B f) (σ↓ : Tree↓ A B f↓ σ)
    → Cell↓ A B (f↓ ∥ σ↓ ▸ hc θ σ↓) θ 

  has-compositions : {A : Set} (B : A → Set) → Set
  has-compositions B = Σ (has-comps B) (has-fills B)
  
  module _ (Γ : Set) (A : Γ → Set) (B : Σ Γ A → Set) 
    (AKan : has-compositions A)
    (BKan : has-compositions B) where

    first-step : (γ : Γ) (σ : (a : A γ) → B (γ , a)) (a : A γ)
      → Cell↓ (Σ Γ A) B {f = ● ∣ ob [ γ , a ]↑ ▸ [ γ , a ]↑} (■ ∥ ob↓ {!!} ▸ {!!}) {!!} 
    first-step = {!!}

    -- Tree-ap↓ : {Γ : Set} {A : Γ → Set} {B : Σ Γ A → Set}
    --   → {n : ℕ} {γ₀ : Frm Γ n} (γ : Tree Γ γ₀)
    --   → {π₀ : Frm↓ Γ (Π↑ A B) γ₀} (π : Tree↓ Γ (Π↑ A B) π₀ γ)
    --   → (a₀ : Frm↓ Γ A γ₀) (a : Tree↓ Γ A a₀ γ)
    --   → Tree↓ (Σ Γ A) B (Frm-ap↓ π₀ a₀) (Tree-pr γ a)


    -- Okay, I want to try this in a very special
    -- case: identity composites.

    has-ids : (γ : Γ) (γ-loop : Cell Γ (● ∣ ob [ γ ]↑ ▸ [ γ ]↑))
      → (γ-null : Cell Γ (● ∣ ob [ γ ]↑ ▸ [ γ ]↑ ∣ lf ● [ γ ]↑ ▸ γ-loop))
      → (σ : (a : A γ) → B (γ , a))
      → Cell↓ Γ (Π↑ A B) (■ ∥ ob↓ ⟦ Π↑ A B ∣ σ ⟧↑ ▸ ⟦ Π↑ A B ∣ σ ⟧↑) γ-loop
    has-ids γ γ-loop γ-null σ = Cell-λ↓ (λ { (■ ∥ ob↓ a₀ ▸ a₁) p →
      let a₀↓ = ⟦ A ∣ a₀ ⟧↓
          a₁↓ = ⟦ A ∣ a₁ ⟧↓
      in {!!} })

    -- Indeed.  So it's a bit like I expected.  We do indeed get
    -- two elements in the same fiber together with a path between
    -- them.  But how do we finish?

    -- Need, I think, to get our J-principle or something into
    -- the game, right?  So the first step is something like, this
    -- works when we have a null-homotopy in the fiber, and we
    -- can reduce to that case.

    -- Okay, I've been thinking more about opetopic J.  Here's what
    -- seems to be the case: given the triangle rule, if you have
    -- for a fixed tree σ, a Kan fibration over the space of pairs
    -- consisting of a target and a filler, then you can eliminate
    -- into that fibration.  This is just because Kan conditions in
    -- the base will give you the triangle, which becomes a path
    -- in the space of pairs.  And then that becomes a guy you can
    -- transport by.
    

-}
