{-# OPTIONS --without-K #-}

module Categories.Cat1to2 where

open import Base

open import Categories.Cat1
open import Categories.Cat2


concrete₁→₂ : ∀ {ℓ} {ℓ′} {ℓ″} → Concrete₁ {ℓ} {ℓ′} {ℓ″} → Concrete₂ {ℓ} {ℓ′} {ℓ″}
concrete₁→₂ C = record {
                  obj = obj;
                  obj⁺ = obj⁺;
                  hom = hom;
                  hom⁺ = hom⁺;
                  conf = conf′;
                  ident′ = ident′;
                  cmp′ = cmp′;
                  unitˡ = unitˡ;
                  unitʳ = unitʳ;
                  assoc = assoc } where
  open Concrete₁ C

  conf′ : {x y : obj} (f : hom′ x y) → is-truncated ⟨0⟩ (hfiber hom⁺ f)
  conf′ f = truncated-is-truncated-S ⟨-1⟩ (conf f)

  unitˡ : {x y : obj} (f : hom x y) → cmp (ident y) f ≡ f
  unitˡ {x} {y} f = ap π₁ (π₁ (conf (hom⁺ f) (cmp (ident y) f , (π₂ (cmp′ (ident y) f) ∘ ap (λ h → h ◯ hom⁺ f) (π₂ (ident′ y)))) (f , refl)))

  unitʳ : {x y : obj} (f : hom x y) → cmp f (ident x) ≡ f
  unitʳ {x} {y} f = ap π₁ (π₁ (conf (hom⁺ f) (cmp f (ident x) , (π₂ (cmp′ f (ident x)) ∘ ap (λ h → hom⁺ f ◯ h) (π₂ (ident′ x)))) (f , refl)))

  assoc : {w x y z : obj} (h : hom y z) (g : hom x y) (f : hom w x) → cmp (cmp h g) f ≡ cmp h (cmp g f)
  assoc h g f = ap π₁ (π₁ (conf (hom⁺ h ◯ (hom⁺ g ◯ hom⁺ f)) (cmp (cmp h g) f , (π₂ (cmp′ (cmp h g) f) ∘ ap (λ k → k ◯ hom⁺ f) (π₂ (cmp′ h g)))) (cmp h (cmp g f) , (π₂ (cmp′ h (cmp g f)) ∘ ap (λ k → hom⁺ h ◯ k) (π₂ (cmp′ g f))))))
