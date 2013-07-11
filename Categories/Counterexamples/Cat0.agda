module Categories.Counterexamples.Cat0 where

open import Base

open import Categories.Cat0


notmap-dom : ∀ {i j} {X : Set i} {Y : Set j} → ¬ (X → Y) → ¬ (¬ X)
notmap-dom n u = n (abort ◯ u)

notmap-cod : ∀ {i j} {X : Set i} {Y : Set j} → ¬ (X → Y) → ¬ Y
notmap-cod n y = n (cst y)


module _ {ℓ ℓ′} (C : Concrete₀ {ℓ} {ℓ′}) where

  open Concrete₀ C

  -- an category in Concrete₀ cannot contain two objects, such that
  -- neither has a map to the other
  no-disjoint : {x y : obj} → ¬ (hom x y) → ¬ (¬ (hom y x))
  no-disjoint u v = (notmap-dom u) (notmap-cod v)