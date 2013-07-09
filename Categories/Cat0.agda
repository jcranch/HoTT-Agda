{-# OPTIONS --without-K #-}

module Categories.Cat0 where

open import Base


-- The special case of 0-full subcategories, has been implemented in a
-- highly degenerate fashion for ease. We provide a full version
-- Concrete′₀ also, in order to illustrate the pattern and in order to
-- improve connections to higher subcategories.


record Concrete₀ {ℓ} : Set (suc ℓ) where
  field
    obj : Set ℓ
    obj⁺ : obj → Set ℓ

  hom : obj → obj → Set ℓ
  hom x y = obj⁺ x → obj⁺ y


record Concrete′₀ {ℓ} : Set (suc ℓ) where
  field
    obj : Set ℓ
    obj⁺ : obj → Set ℓ

  hom′ : obj → obj → Set ℓ
  hom′ x y = obj⁺ x → obj⁺ y

  field
    hom : obj → obj → Set ℓ
    hom⁺ : {x y : obj} → hom x y → hom′ x y
    conf : {x y : obj} (f : hom′ x y) → is-truncated ⟨-2⟩ (hfiber hom⁺ f)


concrete₀-prime : ∀ {ℓ} → Concrete₀ {ℓ} → Concrete′₀ {ℓ}
concrete₀-prime C = record {
  obj = obj;
  obj⁺ = obj⁺;
  hom = hom;
  hom⁺ = λ f → f;
  conf = pathto-is-contr } where
  open Concrete₀ C
