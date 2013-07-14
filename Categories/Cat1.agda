{-# OPTIONS --without-K #-}

module Categories.Cat1 where

open import Base



record Concrete₁ {ℓ ℓ′ ℓ″} : Set (suc (max (max ℓ ℓ′) ℓ″)) where
  field
    obj : Set ℓ
    obj⁺ : obj → Set ℓ′

  hom′ : obj → obj → Set ℓ′
  hom′ x y = obj⁺ x → obj⁺ y

  field
    hom : obj → obj → Set ℓ″
    hom⁺ : {x y : obj} → hom x y → hom′ x y
    conf : {x y : obj} (f : hom′ x y) → is-truncated ⟨-1⟩ (hfiber hom⁺ f)
    ident′ : (x : obj) → hfiber hom⁺ (id (obj⁺ x))
    cmp′ : {x y z : obj} (g : hom y z) (f : hom x y) → hfiber hom⁺ (hom⁺ g ◯ hom⁺ f)

  ident : (x : obj) → hom x x
  ident x = π₁ (ident′ x)

  cmp : {x y z : obj} → hom y z → hom x y → hom x z
  cmp g f = π₁ (cmp′ g f)



module _ {ℓ ℓ′ ℓ″} (C : Concrete₁ {ℓ} {ℓ′} {ℓ″}) where

  open Concrete₁ C

  is-equiv₁ : {x y : obj} → hom x y → Set (max ℓ′ ℓ″)
  is-equiv₁ f = Σ (is-equiv $ hom⁺ f) (λ e → hfiber hom⁺ $ inverse (hom⁺ f , e))