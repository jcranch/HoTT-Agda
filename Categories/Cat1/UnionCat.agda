{-# OPTIONS --without-K #-}

module Categories.Cat1.UnionCat where

open import Base
open import HLevelFun
open import Types.Sum

open import Categories.Cat1


_⊔₁_ : ∀ {ℓ} → Concrete₁ {ℓ} → Concrete₁ {ℓ} → Concrete₁ {ℓ}
C ⊔₁ D = record {
           obj = obj;
           obj⁺ = obj⁺;
           hom = hom;
           hom⁺ = λ {x} {y} → hom⁺ {x} {y};
           conf = λ {x} {y} → conf {x} {y};
           ident′ = ident′;
           cmp′ = λ {x} {y} {z} → cmp′ {x} {y} {z} } where

  open Concrete₁ C hiding (hom′) renaming (obj to C-obj ; obj⁺ to C-obj⁺ ; hom to C-hom ; hom⁺ to C-hom⁺ ; conf to C-conf ; ident′ to C-ident′ ; cmp′ to C-cmp′ ; ident to C-ident)
  open Concrete₁ D hiding (hom′) renaming (obj to D-obj ; obj⁺ to D-obj⁺ ; hom to D-hom ; hom⁺ to D-hom⁺ ; conf to D-conf ; ident′ to D-ident′ ; cmp′ to D-cmp′ ; ident to D-ident)

  obj : Set _
  obj = C-obj ⊔ D-obj

  obj⁺ : obj → Set _
  obj⁺ (inl x) = C-obj⁺ x
  obj⁺ (inr x) = D-obj⁺ x

  hom : obj → obj → Set _
  hom (inl x) (inl y) = C-hom x y
  hom (inl x) (inr y) = ⊥
  hom (inr x) (inl y) = ⊥
  hom (inr x) (inr y) = D-hom x y

  hom′ : obj → obj → Set _
  hom′ x y = (obj⁺ x) → (obj⁺ y)

  hom⁺ : {x y : obj} → hom x y → hom′ x y
  hom⁺ {inl x} {inl y} f = C-hom⁺ f
  hom⁺ {inl x} {inr y} ()
  hom⁺ {inr x} {inl y} ()
  hom⁺ {inr x} {inr y} f = D-hom⁺ f

  ident′ : (x : obj) → hfiber (hom⁺ {x} {x}) (id (obj⁺ x))
  ident′ (inl x) = C-ident′ x
  ident′ (inr x) = D-ident′ x
 
  cmp′ : {x y z : obj} (g : hom y z) (f : hom x y) → hfiber (hom⁺ {x} {z}) (hom⁺ {y} {z} g ◯ hom⁺ {x} {y} f)
  cmp′ {x} {inr y} {inl z} () f
  cmp′ {x} {inl y} {inr z} () f
  cmp′ {inr x} {inl y} {z} g ()
  cmp′ {inl x} {inr y} {z} g ()
  cmp′ {inl x} {inl y} {inl z} g f = C-cmp′ {x} {y} {z} g f
  cmp′ {inr x} {inr y} {inr z} g f = D-cmp′ {x} {y} {z} g f

  conf : {x y : obj} → is-truncated-map ⟨-1⟩ (hom⁺ {x} {y})
  conf {inl x} {inl y} f a = C-conf f a
  conf {inl x} {inr y} f (() , _)
  conf {inr x} {inl y} f (() , _)
  conf {inr x} {inr y} f a = D-conf f a