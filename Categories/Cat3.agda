{-# OPTIONS --without-K #-}

module Categories.Cat3 where

open import Base


record Concrete₃ {ℓ ℓ′ ℓ″} : Set (suc (max (max ℓ ℓ′) ℓ″)) where
  field
    obj  : Set ℓ
    obj⁺ : obj → Set ℓ′

  hom′ : obj → obj → Set ℓ′
  hom′ x y = obj⁺ x → obj⁺ y

  field
    hom : obj → obj → Set ℓ″
    hom⁺ : {x y : obj} → hom x y → hom′ x y
    conf : {x y : obj} (f : hom′ x y) → is-truncated ⟨1⟩ (hfiber hom⁺ f)
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

  assoc²₁ : {v w x y z : obj} (h : hom y z) (g : hom x y) (f : hom w x) (e : hom v w) → cmp (cmp (cmp h g) f) e ≡ cmp h (cmp g (cmp f e))
  assoc²₁ h g f e = (ap (λ x → cmp x e) (assoc h g f) ∘ assoc h (cmp g f) e) ∘ ap (cmp h) (assoc g f e)
  assoc²₂ : {v w x y z : obj} (h : hom y z) (g : hom x y) (f : hom w x) (e : hom v w) → cmp (cmp (cmp h g) f) e ≡ cmp h (cmp g (cmp f e))
  assoc²₂ h g f e = assoc (cmp h g) f e ∘ assoc h g (cmp f e)

  id²₁ : {x y z : obj} (g : hom y z) (f : hom x y) → cmp (cmp g (ident y)) f ≡ cmp g f
  id²₁ {x} {y} {z} g f = assoc g (ident y) f ∘ ap (cmp g) (unitˡ f)

  id²₂ : {x y z : obj} (g : hom y z) (f : hom x y) → cmp (cmp g (ident y)) f ≡ cmp g f
  id²₂ g f = ap (λ x → cmp x f) (unitʳ g)

  field
    assoc² : {v w x y z : obj} (h : hom y z) (g : hom x y) (f : hom w x) (e : hom v w) → assoc²₁ h g f e ≡ assoc²₂ h g f e

    id² : {x y z : obj} (g : hom y z) (f : hom x y) → id²₁ g f ≡ id²₂ g f
