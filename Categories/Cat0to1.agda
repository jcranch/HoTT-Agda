{-# OPTIONS --without-K #-}

open import Base

open import Categories.Cat0
open import Categories.Cat1

module Categories.Cat0to1 where


module _ {ℓ ℓ′ ℓ″} (C : Concrete′₀ {ℓ} {ℓ′} {ℓ″}) where

  open Concrete′₀ C

  concrete′₀→₁ : Concrete₁ {ℓ} {ℓ′} {ℓ″}
  concrete′₀→₁ = record {
    obj = obj;
    obj⁺ = obj⁺;
    hom = hom;
    hom⁺ = hom⁺;
    conf = conf′;
    ident′ = ident′;
    cmp′ = cmp′ } where
    conf′ : {x y : obj} (f : hom′ x y) → is-truncated ⟨-1⟩ (hfiber hom⁺ f)
    conf′ f = truncated-is-truncated-S ⟨-2⟩ (conf f)
    ident′ : (x : obj) → hfiber hom⁺ (id (obj⁺ x))
    ident′ x = π₁ (conf (id (obj⁺ x)))
    cmp′ : {x y z : obj} (g : hom y z) (f : hom x y) → hfiber hom⁺ (hom⁺ g ◯ hom⁺ f)
    cmp′ g f = π₁ (conf (hom⁺ g ◯ hom⁺ f))

  is-equiv′₀→₁ : {x y : obj} {f : hom x y} → is-equiv′₀ f → is-equiv₁ concrete′₀→₁ f
  is-equiv′₀→₁ {x} {y} {f} e = e , (π₁ $ conf $ inverse (hom⁺ f , e))


module _ {ℓ} {ℓ′} (C : Concrete₀ {ℓ} {ℓ′}) where

  open Concrete₀ C

  concrete₀→₁ : Concrete₁ {ℓ} {ℓ′} {ℓ′}
  concrete₀→₁ = concrete′₀→₁ $ concrete₀-prime C

  is-equiv₀→₁ : {x y : obj} {f : hom x y} → is-equiv₀ f → is-equiv₁ concrete₀→₁ f
  is-equiv₀→₁ = is-equiv′₀→₁ (concrete₀-prime C)