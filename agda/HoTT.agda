{-# OPTIONS --without-K --rewriting #-}

open import Base
open import Opetopes
open import OpetopicType
open import J

module HoTT where

  _==_ : {A : Set} → A → A → Set
  _==_ {A} a₀ a₁ = Cell A (□ a₀ ▹ a₁)

  refl : {A : Set} (x : A) → x == x
  refl x = Cell-refl x ○

  transport : {A : Set} (B : A → Set) {x y : A} (p : x == y) → B x → B y
  transport {A} B {x} {y} p x↓ = J A x (B ∘ fst) x↓ y p

  ! : {A : Set} {x y : A} → x == y → y == x
  ! {x = x} p = transport (λ y → y == x) p (Cell-refl x ○)

  hfiber : {A B : Set} (f : A → B) → B → Set
  hfiber {A = A} f b = Σ A (λ a → f a == b)

  --is-contr : Set → Set
  --is-contr A = Σ A (λ a₀ → (a₁ : A) → a₀ == a₁)

  is-equiv : {A B : Set} (f : A → B) → Set
  is-equiv {B = B} f = (b : B) → is-contr (hfiber f b)

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

  ide : (A : Set) → A ≃ A
  rel        (ide A) x y = x == y
  coh        (ide A) x = x
  coe        (ide A) x = x
  coh-rel    (ide A) x = refl x
  coe-rel    (ide A) x = refl x
  coh-unique (ide A) x y p = p
  coe-unique (ide A) x y p = p

  _∘ₑ_ : {A B C : Set} → B ≃ C → A ≃ B → A ≃ C
  rel        (_∘ₑ_ {B = B} g f) a c = Σ B λ b → (rel g b c × rel f a b)
  coh        (g ∘ₑ f) = coh g ∘ coh f
  coe        (g ∘ₑ f) = coe f ∘ coe g
  coh-rel    (g ∘ₑ f) a = coh f a , coh-rel g (coh f a) , coh-rel f a
  coe-rel    (g ∘ₑ f) c = coe g c , coe-rel g c , coe-rel f (coe g c)
  coh-unique (_∘ₑ_ {B = B} g f) a c (b , r₂ , r₁) =
    let r = transport (λ b → rel g b c) (! {A = B} (coh-unique f a b r₁)) r₂
    in coh-unique g (coh f a) c r
  coe-unique (_∘ₑ_ {B = B} g f) a c (b , r₂ , r₁) =
    let r = transport (λ b → rel f a b) (coe-unique g b c r₂) r₁
    in coe-unique f a (coe g c) r
