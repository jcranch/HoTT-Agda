{-# OPTIONS --without-K #-}

module Categories.Examples.AKS where

open import Base
open import Categories.Cat2



record PreCategory1 {i : Level} : Set (suc i) where
  field
    obj : Set i
    hom : obj → obj → Set i
    homsets : (a b : obj) → is-set (hom a b)
    ident : (a : obj) → hom a a
    cmp : {a b c : obj} → hom b c → hom a b → hom a c
    unitˡ : {a b : obj} (f : hom a b) → cmp (ident b) f ≡ f
    unitʳ : {a b : obj} (f : hom a b) → cmp f (ident a) ≡ f
    assoc : {a b c d : obj} (h : hom c d) (g : hom b c) (f : hom a b) → cmp (cmp h g) f ≡ cmp h (cmp g f)



module precategories {i} (C : PreCategory1 {i}) where
  open PreCategory1 C

  record is-iso {a b : obj} (f : hom a b) : Set i where
    constructor make-iso
    field
      g : hom b a
      η : cmp g f ≡ ident a
      ε : cmp f g ≡ ident b
 
  iso-all-paths : {a b : obj} (f : hom a b) (u v : is-iso f) → u ≡ v
  iso-all-paths {a} {b} f (make-iso g η ε) (make-iso g′ η′ ε′) with (! (unitʳ g) ∘ ap (cmp g) (! ε′) ∘ ! (assoc g f g′) ∘ ap (flip cmp g′) η ∘ unitˡ g′)
  iso-all-paths {a} {b} f (make-iso g η ε) (make-iso .g η′ ε′) | refl = ap₂ (make-iso g) (π₁ (homsets a a (cmp g f) (ident a) η η′)) (π₁ (homsets b b (cmp f g) (ident b) ε ε′))

  iso-is-prop : {a b : obj} (f : hom a b) → is-prop (is-iso f)
  iso-is-prop f = all-paths-is-prop (iso-all-paths f)

  _≅_ : obj → obj → Set i
  a ≅ b = Σ (hom a b) is-iso

  id-to-iso : {a b : obj} → a ≡ b → a ≅ b
  id-to-iso {a} refl = ident a , make-iso (ident a) (unitˡ (ident a)) (unitˡ (ident a))

  iso-is-set : (a b : obj) → is-set (a ≅ b)
  iso-is-set a b = Σ-is-truncated ⟨0⟩ (homsets a b) (λ f → prop-is-set (iso-is-prop f)) 



record Category1 {i : Level} : Set (suc i) where
  field
    P : PreCategory1 {i}

  open PreCategory1 P
  open precategories P

  field
    cat-univalence : {a b : obj} → is-equiv (id-to-iso {a} {b})

  obj-is-1type : is-truncated ⟨1⟩ obj
  obj-is-1type a b = equiv-types-truncated ⟨0⟩ ((id-to-iso {a} {b} , cat-univalence {a} {b}) ⁻¹) (iso-is-set a b)



module _ {i} (C : Category1 {i}) where
  open Category1 C
  open PreCategory1 P
  open precategories P

  private
    obj⁺ : obj → Set i
    obj⁺ x = Σ obj (λ y → hom y x)

    obj⁺-is-1type : (x : obj) → is-truncated ⟨1⟩ (obj⁺ x)
    obj⁺-is-1type x = Σ-is-truncated ⟨1⟩ obj-is-1type (λ y → truncated-is-truncated-S ⟨0⟩ (homsets y x))

    obj⁺→obj⁺-is-1type : (x y : obj) → is-truncated ⟨1⟩ (obj⁺ x → obj⁺ y)
    obj⁺→obj⁺-is-1type x y = →-is-truncated ⟨1⟩ (obj⁺-is-1type y)

    hom⁺ : {x y : obj} (f : hom x y) → obj⁺ x → obj⁺ y
    hom⁺ {x} {y} f (z , g) = z , cmp f g

    ident′ : (x : obj) → hfiber hom⁺ (id (obj⁺ x))
    ident′ x = ident x , (funext F) where
      F : (a : obj⁺ x) → hom⁺ (ident x) a ≡ id (obj⁺ x) a
      F a = ap (_,_ (π₁ a)) (unitˡ (π₂ a))

    cmp′ : {x y z : obj} (g : hom y z) (f : hom x y) → hfiber hom⁺ (hom⁺ g ◯ hom⁺ f)
    cmp′ g f = cmp g f , (funext F) where
      F : (a : obj⁺ _) → hom⁺ (cmp g f) a ≡ (hom⁺ g ◯ hom⁺ f) a
      F a = ap (_,_ (π₁ a)) (assoc g f (π₂ a))

    conf : {x y : obj} (f : obj⁺ x → obj⁺ y) → is-truncated ⟨0⟩ (hfiber hom⁺ f)
    conf {x} {y} f = Σ-is-truncated ⟨0⟩ (homsets x y) (λ g → obj⁺→obj⁺-is-1type x y (hom⁺ g) f)

  aks-to-concrete : Concrete₂
  aks-to-concrete = record {
    obj = obj;
    obj⁺ = obj⁺;
    hom = hom;
    hom⁺ = hom⁺;
    conf = conf;
    ident′ = ident′;
    cmp′ = cmp′;
    unitˡ = unitˡ;
    unitʳ = unitʳ;
    assoc = assoc }
  