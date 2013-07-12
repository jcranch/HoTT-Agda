module Categories.Examples.Diagrams where

open import Base
open import Categories.Cat0
open import Categories.Cat1


arrow : ∀ {ℓ ℓ′} → Concrete₀ {ℓ} {ℓ′}
arrow {ℓ} {ℓ′} = record {
  obj = bool;
  obj⁺ = obj⁺ } where
  obj⁺ : bool → Set ℓ′
  obj⁺ true = ⊥
  obj⁺ false = ⊤

indiscrete : ∀ {ℓ ℓ′} (X : Set ℓ) → Concrete₀ {ℓ} {ℓ′}
indiscrete {ℓ} {ℓ′} X = record {
  obj = X;
  obj⁺ = cst ⊤ }
