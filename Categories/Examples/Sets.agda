{-# OPTIONS --without-K #-}

module Categories.Examples.Sets where

open import Base

open import Categories.Cat0
open import Categories.Examples.Delta -- for finite sets


-- category of homotopy types
CType : ∀ {i} → Concrete₀ {suc i}
CType {i} = record {
  obj = Set i;
  obj⁺ = lift (suc i) }

-- category of homotopy n-types
CType≤ : ∀ {i} → ℕ₋₂ → Concrete₀ {suc i}
CType≤ {i} n = record {
  obj = Type≤ n i;
  obj⁺ = lift (suc i) ◯ π₁ }

-- one model for the terminal category
CCtr : ∀ {i} → Concrete₀ {suc i}
CCtr = CType≤ ⟨-2⟩

-- one model for the category with two objects and one nontrivial
-- arrow between them
CProp : ∀ {i} → Concrete₀ {suc i}
CProp = CType≤ ⟨-1⟩

-- the category of sets
CSet : ∀ {i} → Concrete₀ {suc i}
CSet = CType≤ ⟨0⟩

-- finite sets as modelled by Fin
CFinSet : Concrete₀ {zero}
CFinSet = record {
  obj = ℕ;
  obj⁺ = Fin }