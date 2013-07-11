{-# OPTIONS --without-K #-}

module Categories.Examples.Sets where

open import Base
open import HLevelFun
open import Categories.Cat0
open import Categories.Cat1
open import Categories.Examples.Delta -- for finite sets


-- category of homotopy types
CType : ∀ {i} → Concrete₀ {suc i} {i}
CType {i} = record {
  obj = Set i;
  obj⁺ = id (Set i) }

-- category of homotopy n-types
CType≤ : ∀ {i} → ℕ₋₂ → Concrete₀ {suc i} {i}
CType≤ {i} n = record {
  obj = Type≤ n i;
  obj⁺ = π₁ }

-- one model for the terminal category
CCtr : ∀ {i} → Concrete₀ {suc i} {i}
CCtr = CType≤ ⟨-2⟩

-- one model for the category with two objects and one nontrivial
-- arrow between them
CProp : ∀ {i} → Concrete₀ {suc i} {i}
CProp = CType≤ ⟨-1⟩

-- the category of sets
CSet : ∀ {i} → Concrete₀ {suc i} {i}
CSet = CType≤ ⟨0⟩

-- finite sets as modelled by Fin
CFinSet : Concrete₀ {zero} {zero}
CFinSet = record {
  obj = ℕ;
  obj⁺ = Fin }

-- homotopy types and n-truncated maps
CTypeFib : ∀ {i} → ℕ₋₂ → Concrete₁ {suc i} {i} {i}
CTypeFib {i} n = record {
  obj = Set i;
  obj⁺ = id (Set i);
  hom = λ X Y → Σ (X → Y) (is-truncated-map n);
  hom⁺ = π₁;
  conf = conf;
  ident′ = ident′;
  cmp′ = cmp′ } where

  conf : {X Y : Set i} (f : X → Y) → is-truncated ⟨-1⟩ (hfiber π₁ f)
  conf f = is-truncated-map-π₁ ⟨-1⟩ (λ g → Π-is-truncated ⟨-1⟩ (λ x → is-truncated-is-prop n)) f

  ident′ : (X : Set i) → hfiber π₁ (id (id (Set i) X))
  ident′ X = (id X , is-truncated-map-id n X) , refl

  cmp′ : {X Y Z : Set i} (g : Σ (Y → Z) (is-truncated-map n)) (f : Σ (X → Y) (is-truncated-map n)) → hfiber π₁ (π₁ g ◯ π₁ f)
  cmp′ (g , G) (f , F) = ((g ◯ f) , is-truncated-map-compose g f n G F) , refl