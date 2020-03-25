{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Base

module Experiment where

  record Poly (I : 𝕌) : 𝕌 where
    field
      γ : I → 𝕌
      ρ : {i : I} → γ i → 𝕌
      τ : {i : I} {c : γ i} → ρ c → I

  open Poly

  ⟦_⟧ : {I : 𝕌} (P : Poly I) → (I → 𝕌) → (I → 𝕌)
  ⟦ P ⟧ X i = Σ (γ P i) (λ c → (p : ρ P c) → X (τ P p))


  mutual

    record 𝕄 (I : 𝕌) : 𝕌 where
      field
        P : 𝕄Type 𝕌𝕄

    postulate
      𝕌𝕄 : 𝕄 ⊤
      _↑_ : {I : 𝕌} (M : 𝕄 I) (X : I → 𝕌) → 𝕄 (Σ I X)
      [_]+ : {I : 𝕌} (M : 𝕄 I) → 𝕄 (Σ I {!!})

    record 𝕄Type {I : 𝕌} (M : 𝕄 I) : 𝕌 where
      coinductive
      field
        A : I → 𝕌 
        B : 𝕄Type [ M ↑ A ]+

  open 𝕄
  open 𝕄Type
  
  -- postulate

  --   𝕄 : 𝕌 → 𝕌
  --   P : {I : 𝕌} (M : 𝕄 I) → Poly I
  --   _↑_ : {I : 𝕌} (M : 𝕄 I) (X : I → 𝕌) → 𝕄 (Σ I X)
  --   [_]+ : {I : 𝕌} (M : 𝕄 I) → 𝕄 (Σ I (γ (P M)))

  -- module _ {I : 𝕌} (M : 𝕄 I) (X : 𝕄Type M) where

  --   ATr : I → 𝕌
  --   ATr = ⟦ P M ⟧ (A X)

  --   -- Shit!  So we can already say what the space of compositions is
  --   -- supposed to be like.  Which means we can already say what an algebra
  --   -- for M is, right?
    
  --   AComp : (i : I) (t : ATr i) → 𝕌
  --   AComp i t = Σ (A X i) (λ a → Σ (γ (P (M ↑ A X)) (i , a)) (λ m → A (B X) ((i , a) , m)))


