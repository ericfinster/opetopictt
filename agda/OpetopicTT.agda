{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT

module OpetopicTT where

  data Frm (X : Set) : Set 
  data Frm↓ {X : Set} (Y : X → Set) : Frm X → Set

  data Web (X : Set) : Frm X → Set
  data Web↓ {X : Set} (Y : X → Set) : 
    {f : Frm X} (f↓ : Frm↓ Y f) (w : Web X f) → Set 

  postulate
  
    Pos : (X : Set) {f : Frm X} → Web X f → Set
    Pos↓ : {X : Set} (Y : X → Set)
      → {f : Frm X} {f↓ : Frm↓ Y f}
      → {w : Web X f} (w↓ : Web↓ Y f↓ w)
      → Pos X w → Set

    Typ : (X : Set) {f : Frm X} {w : Web X f}
      → Pos X w → Frm X 
    Typ↓ : {X : Set} (Y : X → Set)
      → {f : Frm X} {f↓ : Frm↓ Y f}
      → {w : Web X f} {w↓ : Web↓ Y f↓ w}
      → {p : Pos X w} (p↓ : Pos↓ Y w↓ p)
      → Frm↓ Y (Typ X p) 

    Cell : (X : Set) → Frm X → Set
    Cell↓ : {X : Set} (Y : X → Set) 
      → {f : Frm X} (f↓ : Frm↓ Y f)
      → (c : Cell X f) → Set 
    
  data Frm X where
    ● : X → X → Frm X 
    ⟨_,_,_,_⟩ : (f : Frm X) (c : Cell X f)
      → (w : Web X f) (δ : (p : Pos X w) → Cell X (Typ X p))
      → Frm X 
    
  data Frm↓ {X} Y where
    ●↓ : {x₀ x₁ : X} → Y x₀ → Y x₁ → Frm↓ Y (● x₀ x₁)
    ⟪_,_,_,_⟫ : {f : Frm X} (f↓ : Frm↓ Y f)
      → {c : Cell X f} (c↓ : Cell↓ Y f↓ c)
      → {w : Web X f} (w↓ : Web↓ Y f↓ w)
      → {δ : (p : Pos X w) → Cell X (Typ X p)}
      → (δ↓ : (p : Pos X w) (p↓ : Pos↓ Y w↓ p) → Cell↓ Y (Typ↓ Y p↓) (δ p))
      → Frm↓ Y ⟨ f , c , w , δ ⟩ 

  data Web X where
  data Web↓ {X} Y where 


  -- frm-fst : (X : Set) (Y : X → Set)
  --   → Frm (Σ X Y) 
  --   → Frm X
  -- frm-fst X Y (● x₀ x₁) = ● (fst x₀) (fst x₁)
  -- frm-fst X Y ⟨ f , c , w , δ ⟩ =
  --   ⟨ frm-fst X Y f , {!!} , {!!} , {!!} ⟩  

  -- frm-snd : (X : Set) (Y : X → Set)
  --   → (f : Frm (Σ X Y))
  --   → Frm↓ Y (frm-fst X Y f)

  -- frm-pair : (X : Set) (Y : X → Set)
  --   → (f : Frm X) (f↓ : Frm↓ Y f)
  --   → Frm (Σ X Y) 

  --
  -- Π-types
  --

  -- postulate
  
  --   frm-app : ∀ {ℓ n} (X : Set ℓ) (Y : X → Set ℓ)
  --     → Frm (Π X Y) n
  --     → (f : Frm X n)
  --     → Frm↓ Y f
  
  --   frm-lam : ∀ {ℓ n} (X : Set ℓ) (Y : X → Set ℓ)
  --     → (ϕ : (f : Frm X n) → Frm↓ Y f)
  --     → Frm (Π X Y) n

  --   cell-app : ∀ {ℓ n} (X : Set ℓ) (Y : X → Set ℓ)
  --     → (πf : Frm (Π X Y) n) (πc : Cell (Π X Y) πf)
  --     → (f : Frm X n) (c : Cell X f)
  --     → Cell↓ Y (frm-app X Y πf f) c

  --   cell-lam : ∀ {ℓ n} (X : Set ℓ) (Y : X → Set ℓ)
  --     → (ϕ : (f : Frm X n) → Frm↓ Y f)
  --     → (ψ : (f : Frm X n) (c : Cell X f) → Cell↓ Y (ϕ f) c)
  --     → Cell (Π X Y) (frm-lam X Y ϕ) 

  cell-frm : (X : Set) → Frm (Frm X) → Set

  postulate

    to-cell-frm : (X : Set) (f : Frm (Frm X))
      → cell-frm X f → Cell (Frm X) f 


  --
  --  Cells in cells 
  --

  postulate

    -- This is the easy case, where things work by concatenation....
    frm-concat : (X : Set)
      → (f : Frm X) (cf : Frm (Cell X f))
      → Frm X
      
    web-cell : (X : Set)
      → (f : Frm X) (cf : Frm (Cell X f))
      → Web (Cell X f) cf → Web X (frm-concat X f cf) 

    cell-cell : (X : Set)
      → (f : Frm X) (cf : Frm (Cell X f))
      → Cell (Cell X f) cf ≡ Cell X (frm-concat X f cf) 


  --
  --  Cells in Frames
  --

  -- A model for the fibration Cell (Frm X) : Frm (Frm X) → Set 
  cell-frm X (● (● x₀ y₀) (● x₁ y₁)) =
    Cell X (● x₀ x₁) × Cell X (● y₀ y₁)
  cell-frm X (● ⟨ f₀ , c₀ , w₀ , δ₀ ⟩ ⟨ f₁ , c₁ , w₁ , δ₁ ⟩) =
    -- So the point is that here, I simply want to say
    -- "make all the components equal"
    Σ (cell-frm X (● f₀ f₁)) (λ f₀≡f₁ →
     Cell↓ (Cell X) {● f₀ f₁} (●↓ c₀ c₁) (to-cell-frm X (● f₀ f₁) f₀≡f₁))
    -- Right, and now there will be more cases for w and δ ...
  cell-frm X ⟨ f , c , w , δ ⟩ =
    Σ (cell-frm X f) (λ f≡ →
    
      Cell↓ (Cell X) {f} {!!} (to-cell-frm X f f≡))

  --
  --  Cells in Webs
  --

  --  As above, you're going to want this to be defined by induction
  --  on the structure of the web.



  postulate


    cell-frm-cell : (X : Set) (f : Frm X)
      → Frm (Cell X f)
      → Cell (Frm X) {!!}  

    web-frm-frm : (X : Set) (f : Frm X)
      → Frm (Web X f)
      → Frm (Frm X) 
      
    web-frm-web : (X : Set) (f : Frm X)
      → (fw : Frm (Web X f))
      → Web (Frm X) (web-frm-frm X f fw)

    cell-● : (X : Set) (x₀ x₁ y₀ y₁ : X)
      → Cell X (● x₀ x₁)
      → Cell X (● y₀ y₁)
      → Cell (Frm X) (● (● x₀ y₀) (● x₁ y₁)) 

    cell-⟨⟩ : (X : Set)
      → (f : Frm (Frm X))
      → (σ : Cell (Frm X) f)
      → Cell (Frm X) ⟨ f , {!!} , {!!} , {!!} ⟩ 


    
  data Frm≡ (X : Set) : Frm X → Frm X → Set where
    ●= : (x₀ x₁ : X) (p : x₀ ≡ x₁)
         (y₀ y₁ : X) (q : y₀ ≡ y₁)
         → Frm≡ X (● x₀ y₀) (● x₁ y₁) 
  
