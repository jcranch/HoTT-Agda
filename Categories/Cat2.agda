{-# OPTIONS --without-K #-}

module Categories.Cat2 where

open import Base


record Concrete₂ {ℓ} : Set (suc ℓ) where
  field
    obj : Set ℓ
    obj⁺ : obj → Set ℓ

  hom′ : obj → obj → Set ℓ
  hom′ x y = obj⁺ x → obj⁺ y

  field
    hom : obj → obj → Set ℓ
    hom⁺ : {x y : obj} → hom x y → hom′ x y
    conf : {x y : obj} (f : hom′ x y) → is-truncated ⟨0⟩ (hfiber hom⁺ f)
    ident′ : (x : obj) → hfiber hom⁺ (id (obj⁺ x))
    cmp′ : {x y z : obj} (g : hom y z) (f : hom x y) → hfiber hom⁺ (hom⁺ g ◯ hom⁺ f)

  ident : (x : obj) → hom x x
  ident x = π₁ (ident′ x)

  cmp : {x y z : obj} → hom y z → hom x y → hom x z
  cmp g f = π₁ (cmp′ g f)

  field
    unitˡ : {x y : obj} (f : hom x y) → cmp (ident y) f ≡ f
    unitʳ : {x y : obj} (f : hom x y) → cmp f (ident x) ≡ f
    assoc : {w x y z : obj} (h : hom y z) (g : hom x y) (f : hom w x) → cmp (cmp h g) f ≡ cmp h (cmp g f)
