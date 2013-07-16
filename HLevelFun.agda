{-# OPTIONS --without-K #-}

-- A collection of miscellaneous extra facts about h-levels, mostly
-- using advanced techniques to prove.

module HLevelFun where

-- hlevel restrictions on maps

open import Base
open import Equivalence.Alternative


change-contr-basepoint : ∀ {i} {A : Set i} (x : A) → is-contr A → is-contr A
change-contr-basepoint x (y , e) = x , (λ z → (e z) ∘ ! (e x))


injective : ∀ {i j} {A : Set i} {B : Set j} → (A → B) → Set (max i j)
injective f = (∀ {a₁ a₂} → f a₁ ≡ f a₂ → a₁ ≡ a₂)

-- injections to sets have propositions as fibres
injection-to-set : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) → is-set B → injective f → (b : B) → is-prop (hfiber f b)
injection-to-set f sB inj b = all-paths-is-prop lemma where
  lemma : (u v : hfiber f b) → u ≡ v
  lemma (a₁ , e₁) (a₂ , e₂) = Σ-eq (inj (e₁ ∘ ! e₂)) (π₁ (sB (f a₂) b _ _))



is-truncated-map : ∀ {i j} {A : Set i} {B : Set j} → ℕ₋₂ → (A → B) → Set (max i j)
is-truncated-map n f = ∀ x → is-truncated n (hfiber f x)



is-truncated-map-id : ∀ {i} (n : ℕ₋₂) (A : Set i) → is-truncated-map n (id A)
is-truncated-map-id n A x = contr-is-truncated n (pathto-is-contr x)



module _ {i j k} {A : Set i} {B : Set j} {C : Set k} (g : B → C) (f : A → B) where

  iterate-hfiber : (c : C) → hfiber (g ◯ f) c → Σ (hfiber g c) (hfiber f ◯ π₁)
  iterate-hfiber c (a , e) = (f a , e) , (a , refl)

  compose-hfiber : (c : C) → Σ (hfiber g c) (hfiber f ◯ π₁) → hfiber (g ◯ f) c
  compose-hfiber ._ ((._ , refl) , (a , refl)) = a , refl

  iterate-compose : (c : C) (p : Σ (hfiber g c) (hfiber f ◯ π₁)) → iterate-hfiber c (compose-hfiber c p) ≡ p
  iterate-compose .(g (f a)) ((.(f a) , refl) , (a , refl)) = refl

  compose-iterate : (c : C) (p : hfiber (g ◯ f) c) → compose-hfiber c (iterate-hfiber c p) ≡ p
  compose-iterate .(g (f a)) (a , refl) = refl

  iterated-hfiber : (c : C) → is-equiv (iterate-hfiber c)
  iterated-hfiber c = quasinv-is-equiv (iterate-hfiber c) (make-quasinv (compose-hfiber c) (funext (compose-iterate c)) (funext (iterate-compose c)))

  hfiber-iter-equiv : (c : C) → hfiber (g ◯ f) c ≃ Σ (hfiber g c) (hfiber f ◯ π₁)
  hfiber-iter-equiv c = (iterate-hfiber c) , (iterated-hfiber c)

  is-truncated-map-compose : (n : ℕ₋₂) → is-truncated-map n g → is-truncated-map n f → is-truncated-map n (g ◯ f)
  is-truncated-map-compose n G F c = equiv-types-truncated n (hfiber-iter-equiv c ⁻¹) (Σ-is-truncated n (G c) (λ p → F (π₁ p)))



-- Pulling back a fiber bundle along a map
fiber-pull-map : ∀ {i j k} {A : Set i} {B : Set j} (P : B → Set k) (f : A → B) → Σ A (P ◯ f) → Σ B P
fiber-pull-map P f (a , b) = f a , b

fiber-pull-id : ∀ {i j} {B : Set i} (P : B → Set j) → fiber-pull-map P (id B) ≡ id (Σ B P)
fiber-pull-id P = funext (λ _ → refl)

-- relates maps Σ A (P ◯ g ◯ f) → Σ C P
fiber-pull-comp : ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} {P : C → Set l} (g : B → C) (f : A → B) → fiber-pull-map P g ◯ fiber-pull-map (P ◯ g) f ≡ fiber-pull-map P (g ◯ f)
fiber-pull-comp g f = funext (λ _ → refl)

fiber-over-contr : ∀ {i j} {A : Set i} (P : A → Set j) (e : is-contr A) → P (π₁ e) ≃ Σ A P
fiber-over-contr {A = A} P (x , c) = f , quasinv-is-equiv f (make-quasinv g (funext gf) (funext fg)) where
  f : P x → Σ A P
  f a = x , a
  g : Σ A P → P x
  g (y , a) = transport P (c y) a
  gf : (a : P x) → g (f a) ≡ a
  gf a = trans-equal P a (contr-has-all-paths (contr-is-prop (x , c) x x) (c x) refl)
  fg : (a : Σ A P) → f (g a) ≡ a
  fg (y , a) = Σ-eq (! (c y)) (trans-opposite-trans P (c y) a)



module _ {i j} {A : Set i} {P : A → Set j} (x : A) where

  private
    from-hfiber : hfiber (π₁ {P = P}) x → P x
    from-hfiber ((.x , a) , refl) = a

    from-hfiber-is-equiv : (a : P x) → is-contr (hfiber from-hfiber a)
    from-hfiber-is-equiv a = (((x , a) , refl) , refl) , θ where
      θ : (y : hfiber from-hfiber a) → y ≡ ((x , a) , refl) , refl
      θ (((.x , .a) , refl) , refl) = refl

  hfiber-π₁ : hfiber (π₁ {P = P}) x ≃ P x
  hfiber-π₁ = from-hfiber , from-hfiber-is-equiv

is-truncated-map-π₁ : ∀ {i j} {A : Set i} {P : A → Set j} (n : ℕ₋₂) → ((x : A) → is-truncated n (P x)) → is-truncated-map n (π₁ {P = P})
is-truncated-map-π₁ n t x = equiv-types-truncated n (hfiber-π₁ x ⁻¹) (t x)



module _ {i j} {A : Set i} {B : Set j} (f : A → B)
         (e : (x y : A) → is-equiv (ap f {x = x} {y = y})) where

  ap-is-equiv-all-paths : (z : B) (a b : hfiber f z) → a ≡ b
  ap-is-equiv-all-paths .(f b) (a , u) (b , refl) = Σ-eq (π₁ (π₁ ε)) (! (trans-ap (λ y → y ≡ f b) f (π₁ (π₁ ε)) u) ∘ trans-id≡cst (ap f (π₁ (π₁ ε))) u ∘ ap (λ z → ! z ∘ u) (π₂ (π₁ ε)) ∘ opposite-left-inverse u) where
    ε = e a b u

  ap-is-equiv-1-truncated : (z : B) → is-prop (hfiber f z)
  ap-is-equiv-1-truncated = all-paths-is-prop ◯ ap-is-equiv-all-paths
