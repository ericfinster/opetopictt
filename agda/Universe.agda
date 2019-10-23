{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Base
open import OpetopicTypes

module Universe where

  init : {A : 𝕌} (f : Frm A)
    → (σ : Tree A f) (τ : Cell A f)
    → A
  init ● (ob α) _ = α
  init (f ∥ σ ▸ τ) _ _ = init f σ τ

  term : {A : 𝕌} (f : Frm A)
    → (σ : Tree A f) (τ : Cell A f)
    → A
  term ● _ τ = τ
  term (f ∥ σ ▸ τ) _ _ = term f σ τ
  
  postulate

    -- Well, okay, equivalences ....
    Univalence : (A B : 𝕌) →
      Cell 𝕌 (● ∥ ob A ▸ B) ↦ (A → B)
    {-# REWRITE Univalence #-}
    
    Frm-𝕌 : (f : Frm 𝕌)
      → (σ₀ : Tree 𝕌 f) (τ₀ : Cell 𝕌 f)
      → (σ₁ : Tree 𝕌 (f ∥ σ₀ ▸ τ₀))
      → (τ₁ : Cell 𝕌 (f ∥ σ₀ ▸ τ₀))
      → init f σ₀ τ₀ → Frm (term f σ₀ τ₀)
      
    Cell-𝕌 : (f : Frm 𝕌)
      → (σ₀ : Tree 𝕌 f) (τ₀ : Cell 𝕌 f)
      → (σ₁ : Tree 𝕌 (f ∥ σ₀ ▸ τ₀))
      → (τ₁ : Cell 𝕌 (f ∥ σ₀ ▸ τ₀))
      → (i : init f σ₀ τ₀)
      → Cell 𝕌 (f ∥ σ₀ ▸ τ₀ ∥ σ₁ ▸ τ₁) ↦ Cell (term f σ₀ τ₀) (Frm-𝕌 f σ₀ τ₀ σ₁ τ₁ i)

    comp-𝕌-lf : (A : 𝕌)
      → comp (● ∥ ob A ▸ A) (lf ● A) ↦ (λ a → a)

    -- Yeah, you could play around with this so that instead
    -- of a specific choice of decoration, you abstract over
    -- it and evaluate.  Then you need to modify the Univalence
    -- law above.  Maybe it is not so crucial for now ....
    comp-𝕌-nd : (A B C : 𝕌) (s : Tree 𝕌 (● ∥ ob A ▸ B)) (f : B → C)
      → comp (● ∥ ob A ▸ C) (nd ● (ob B) C f (λ p → ob A) (λ p → s)) ↦
        (λ a → f ((comp (● ∥ ob A ▸ B) s) a))

    -- comp : {A : 𝕌} (f : Frm A) → Tree A f → Cell A f
    -- fill : {A : 𝕌} (f : Frm A) (σ : Tree A f) → Cell A (f ∥ σ ▸ comp f σ)

    -- J : {A : 𝕌} (f : Frm A) (σ : Tree A f)
    --   → (P : (τ : Cell A f) (ρ : Cell A (f ∥ σ ▸ τ)) → 𝕌)
    --   → (d : P (comp f σ) (fill f σ))
    --   → (τ : Cell A f) (ρ : Cell A (f ∥ σ ▸ τ)) → P τ ρ

  -- Right.  So you have to finish the task of defining Frm-𝕌, as this clearly
  -- needs to compute.  Not at all sure how to define this function, but
  -- supposing I can, it seems like this is okay.

  -- Note that the general setup covers Cell 𝕌 ●, Univalence covers
  -- dimesnion 1, and this rule coverse all higher ones.

  -- Okay, I see.  So the next step should be to implement the
  -- composition and filling operations and the J-rule to complete
  -- the description.

  -- So, what remains?  Well, we must explain the composition and
  -- filling structure of Σ, Π and our various fibrations.  Hmmm.

  
