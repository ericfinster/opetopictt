{-# OPTIONS --without-K --rewriting --no-positivity-check #-}

open import Base
open import Opetopes

module Slice where

  -- Okay, I'd like to see if there's an inductive definition of the
  -- slice/link at the terminal object.  It seems that the definition
  -- of the cells in the universe makes use of this construction, so
  -- we need to have a reasonable presentation of it ...

  Slice : {n : ℕ} → 𝕆 (S n) → 𝕆 n
  SliceTr : {n : ℕ} (o : 𝕆 (S n)) → ℙ o → ℙ (Slice o)
  Sliceδ : {n : ℕ} (o : 𝕆 (S n)) (p : ℙ o)
    → (s : Pos (SliceTr o p)) → ℙ (Typ (SliceTr o p) s)
  Sliceε : {n : ℕ} (o : 𝕆 (S n)) (p : ℙ o)
    → (s : Pos (SliceTr o p)) → ℙ (Typ (SliceTr o p) s ▸ Sliceδ o p s)

  Slice (● ▸ p) = ●
  Slice (o ▸ p ▸ q) = Slice (o ▸ p) ▸ SliceTr (o ▸ p) q

  SliceTr (● ▸ p) σ = arr
  SliceTr (● ▸ p ▸ .(η (● ▸ p))) (lf .(● ▸ p)) = lf ●
  SliceTr (● ▸ .arr ▸ .(lf ●)) (nd .(● ▸ arr) (lf .●) δ ε) = {!!}
  SliceTr (● ▸ .(δ₁ arr-pos) ▸ ._) (nd .(● ▸ δ₁ arr-pos) (nd .● arr δ₁ ε₁) δ ε) =
    let ih s = SliceTr (● ▸ δ₁ s ▸ ε₁ s) {!ε!} -- 
    in {!!}
    
  -- What you want to do here is to follow the node constructor, while
  -- inspecting σ.  Basically the idea is to only ever call
  -- recursively on the *root* of σ, and duplicate appropriately in
  -- the case where σ is a leaf.  Reminds me of the "initialization"
  -- part of you scala/ocaml untyped grafting algo ....
  SliceTr (o ▸ p ▸ q ▸ r) σ = {!!}

  Sliceδ o p = {!!}
  Sliceε o p = {!!}

  -- Hmm.  Thing is, it doesn't seem to be defined recursively
  -- starting from the top.  Well, okay, so it's like we need to
  -- recurse first and use some extra information which is coming back
  -- from the recursive call.

  -- Yeah, for example, there should be a map on positions, which is
  -- essentially what you are seeing when you look at the labeling in
  -- your implementation.

  -- Okay, I see.  So the only place you can possibly get duplication
  -- is in the lowest dimension (assuming you are just doing the
  -- slice.)

  -- Yep, so in the case of a drop (if the dimension is high enough)
  -- there is no new information, as we may as well pass immediately
  -- to the recursive step and then take a drop.

  -- So that actually looks okay.
