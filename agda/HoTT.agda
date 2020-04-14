{-# OPTIONS --without-K --rewriting #-}

open import Base
open import Opetopes
open import OpetopicType

module HoTT where

  _==_ : {A : Set} → A → A → Set
  _==_ {A} a₀ a₁ = Cell A (□ a₀ ▹ a₁)

  hfiber : {A B : Set} (f : A → B) → B → Set
  hfiber {A = A} f b = Σ A (λ a → f a == b)

  is-contr : Set → Set
  is-contr A = Σ A (λ a₀ → (a₁ : A) → a₀ == a₁)

  is-equiv : {A B : Set} (f : A → B) → Set
  is-equiv {B = B} f = (b : B) → is-contr (hfiber f b)

  infixl 40 _≃_
  
  record _≃_ (A B : Set) : Set₁ where
    field

      rel : A → B → Set
      
      coh : A → B
      coe : B → A
      
      coh-rel : (a : A) → rel a (coh a)
      coe-rel : (b : B) → rel (coe b) b
      
      coh-unique : (a : A) (b : B)
        → rel a b → coh a == b
      coe-unique : (a : A) (b : B)
        → rel a b → a == coe b

  open _≃_ public 
