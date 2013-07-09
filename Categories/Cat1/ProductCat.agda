{-# OPTIONS --without-K #-}

module Categories.Cat1.ProductCat where

open import Base
open import HLevelFun
open import Types.Product
open import Types.Sum

open import Categories.Cat1



_×₁_ : ∀ {ℓ₁ ℓ₂} → Concrete₁ {ℓ₁} → Concrete₁ {ℓ₂} → Concrete₁ {max ℓ₁ ℓ₂}
C ×₁ D = record {
           obj = obj;
           obj⁺ = obj⁺;
           hom = hom;
           hom⁺ = hom⁺;
           conf = conf;
           ident′ = ident′;
           cmp′ = cmp′ } where

  open Concrete₁ C hiding (hom′) renaming (obj to C-obj ; obj⁺ to C-obj⁺ ; hom to C-hom ; hom⁺ to C-hom⁺ ; conf to C-conf ; ident′ to C-ident′ ; cmp′ to C-cmp′ ; ident to C-ident)
  open Concrete₁ D hiding (hom′) renaming (obj to D-obj ; obj⁺ to D-obj⁺ ; hom to D-hom ; hom⁺ to D-hom⁺ ; conf to D-conf ; ident′ to D-ident′ ; cmp′ to D-cmp′ ; ident to D-ident)

  obj = C-obj × D-obj

  obj⁺ : obj → Set _
  obj⁺ (x , y) = C-obj⁺ x ⊔ D-obj⁺ y

  hom : obj → obj → Set _
  hom (x₁ , y₁) (x₂ , y₂) = C-hom x₁ x₂ × D-hom y₁ y₂

  hom′ : obj → obj → Set _
  hom′ x y = (obj⁺ x) → (obj⁺ y)

  hom⁺ : {x y : obj} → hom x y → hom′ x y
  hom⁺ (f , g) = ⊔-funct (C-hom⁺ f) (D-hom⁺ g)

  ident′ : (x : obj) → hfiber hom⁺ (id (obj⁺ x))
  ident′ (x₁ , x₂) = (π₁ (C-ident′ x₁) , π₁ (D-ident′ x₂)) , funext F where
    F : (p : obj⁺ (x₁ , x₂)) → hom⁺ (C-ident x₁ , D-ident x₂) p ≡ p
    F (inl a) = ap inl (happly (π₂ (C-ident′ x₁)) a)
    F (inr b) = ap inr (happly (π₂ (D-ident′ x₂)) b)
 
  cmp′ : {x y z : obj} (g : hom y z) (f : hom x y) → hfiber hom⁺ (hom⁺ g ◯ hom⁺ f)
  cmp′ (g₁ , g₂) (f₁ , f₂) = (π₁ (C-cmp′ g₁ f₁) , π₁ (D-cmp′ g₂ f₂)) , (funext F) where
    F : (p : obj⁺ _) → hom⁺ (_ , _) p ≡ hom⁺ (g₁ , g₂) (hom⁺ (f₁ , f₂) p)
    F (inl a) = ap inl (happly (π₂ (C-cmp′ g₁ f₁)) a)
    F (inr b) = ap inr (happly (π₂ (D-cmp′ g₂ f₂)) b)

  conf : {x y : obj} → is-truncated-map ⟨-1⟩ (hom⁺ {x} {y})
  conf {x} {y} = is-truncated-map-compose (uncurry ⊔-funct) (×-funct C-hom⁺ D-hom⁺) ⟨-1⟩ trunc₁ trunc₂ where
    trunc₁ : is-truncated-map ⟨-1⟩ (uncurry ⊔-funct)
    trunc₁ = ⊔-funct-components
    trunc₂ : is-truncated-map ⟨-1⟩ (×-funct C-hom⁺ D-hom⁺)
    trunc₂ = ×-funct-truncated C-hom⁺ D-hom⁺ ⟨-1⟩ C-conf D-conf