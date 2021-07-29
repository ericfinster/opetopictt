{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT

module OpetopicTT where

  Frm : ∀ {ℓ} (X : Set ℓ) → (n : ℕ) → Set ℓ

  postulate

    Cell : ∀ {ℓ} (X : Set ℓ) {n : ℕ} → Frm X n → Set ℓ
    Web : ∀ {ℓ} (X : Set ℓ) {n : ℕ} → Frm X n → Set ℓ

    Pos : ∀ {ℓ} (X : Set ℓ) {n : ℕ} {f : Frm X n}
      → Web X f → Set ℓ
      
    Typ : ∀ {ℓ} (X : Set ℓ) {n : ℕ} {f : Frm X n}
      → (w : Web X f) (p : Pos X w) → Frm X n 

  Frm X O = X × X
  Frm X (S n) =
    Σ (Frm X n) (λ f →
    Σ (Cell X f) (λ c →
    Σ (Web X f) (λ w →
    Π (Pos X w) (λ p →
      Cell X (Typ X w p)))))
