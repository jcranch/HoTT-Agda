{-# OPTIONS --without-K #-}

module HLevelFun where

-- hlevel restrictions on maps

open import Base
open import Equivalence.Alternative


injective : ∀ {i j} {A : Set i} {B : Set j} → (A → B) → Set (max i j)
injective f = (∀ {a₁ a₂} → f a₁ ≡ f a₂ → a₁ ≡ a₂)

-- injections to sets have propositions as fibres
injection-to-set : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) → is-set B → injective f → (b : B) → is-prop (hfiber f b)
injection-to-set f sB inj b = all-paths-is-prop lemma where
  lemma : (u v : hfiber f b) → u ≡ v
  lemma (a₁ , e₁) (a₂ , e₂) = Σ-eq (inj (e₁ ∘ ! e₂)) (π₁ (sB (f a₂) b _ _))



is-truncated-map : ∀ {i j} {A : Set i} {B : Set j} → ℕ₋₂ → (A → B) → Set (max i j)
is-truncated-map n f = ∀ x → is-truncated n (hfiber f x)



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

