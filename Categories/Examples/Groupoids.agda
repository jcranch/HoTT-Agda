module Categories.Examples.Groupoids where

open import Base

open import Categories.Cat1



module _ {i} {X : Set i} where

  over : (x : X) → Set i
  over x =  Σ X (λ y → y ≡ x)

  over-map : {x y : X} → x ≡ y → over x → over y
  over-map e (a , p) = (a , (p ∘ e))

  -- This is fairly incomprehensible
  over-conf : {x y : X} (f : over x → over y) → is-truncated ⟨-1⟩ (hfiber over-map f)
  over-conf {.y} {y} .(λ ap₁ → π₁ ap₁ , (π₂ ap₁ ∘ refl)) (refl , refl) (refl , refl) = refl , k where
    k : (e : _) → e ≡ _
    k refl = refl

  over-ident : (x : X) → hfiber over-map (id (over x))
  over-ident x = refl , funext F where
    F : (α : over x) → π₁ α , (π₂ α ∘ refl) ≡ α
    F (a , p) = ap (_,_ a) (refl-right-unit p)

  over-cmp : {x y z : X} (g : y ≡ z) (f : x ≡ y) → hfiber over-map (over-map g ◯ over-map f)
  over-cmp {x} {y} {z} g f = (f ∘ g) , funext F where
    F : (α : over x) → π₁ α , (π₂ α ∘ (f ∘ g)) ≡ π₁ α , ((π₂ α ∘ f) ∘ g)
    F (a , p) = ap (_,_ a) (! (concat-assoc p f g))


groupoid : ∀ {i} → Set i → Concrete₁ {i}
groupoid X = record {
  obj = X;
  obj⁺ = over;
  hom = _≡_;
  hom⁺ = over-map;
  conf = over-conf;
  ident′ = over-ident;
  cmp′ = over-cmp } 