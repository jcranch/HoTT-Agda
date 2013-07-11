{-# OPTIONS --without-K #-}

module Categories.Cat0to1 where

open import Base

open import Categories.Cat0
open import Categories.Cat1


concrete′₀→₁ : ∀ {ℓ ℓ′ ℓ″} → Concrete′₀ {ℓ} {ℓ′} {ℓ″} → Concrete₁ {ℓ} {ℓ′} {ℓ″}
concrete′₀→₁ {ℓ} C = record {
                       obj = obj;
                       obj⁺ = obj⁺;
                       hom = hom;
                       hom⁺ = hom⁺;
                       conf = conf′;
                       ident′ = ident′;
                       cmp′ = cmp′ } where
  open Concrete′₀ C
  conf′ : {x y : obj} (f : hom′ x y) → is-truncated ⟨-1⟩ (hfiber hom⁺ f)
  conf′ f = truncated-is-truncated-S ⟨-2⟩ (conf f)
  ident′ : (x : obj) → hfiber hom⁺ (id (obj⁺ x))
  ident′ x = π₁ (conf (id (obj⁺ x)))
  cmp′ : {x y z : obj} (g : hom y z) (f : hom x y) → hfiber hom⁺ (hom⁺ g ◯ hom⁺ f)
  cmp′ g f = π₁ (conf (hom⁺ g ◯ hom⁺ f))

concrete₀→₁ : ∀ {ℓ ℓ′} → Concrete₀ {ℓ} {ℓ′} → Concrete₁ {ℓ} {ℓ′} {ℓ′}
concrete₀→₁ = concrete′₀→₁ ◯ concrete₀-prime
