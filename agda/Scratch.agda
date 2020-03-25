{-# OPTIONS --without-K --rewriting #-}

open import Base

module Scratch where

  postulate
  
    Arr₀ : 𝕌
    Top : Arr₀
    Bot : Arr₀
    Arr₁ : Arr₀ → Arr₀ → 𝕌
    Arrow : Arr₁ Bot Top

    Arr-rec : (X : 𝕌) (top* : X) (bot* : X)
      → (Arr₁* : X → X → 𝕌)
      → (Arrow* : Arr₁* top* bot*)
      → Arr₀ → X

  -- Okay, kind of interesting.  So the idea is kind of like....
  -- well, clearly the representable is the "higher poly monad
  -- on a single generator."

  -- Okay, so can you make sense of this idea of two polymonads,
  -- dependent on each other?  What do we have then?  A polymonad,
  -- that's fine.  And then what?  Well, then a polymonad over
  -- ...

  -- 
      
