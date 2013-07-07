{-# OPTIONS --without-K #-}

open import Types
open import Functions
open import Paths
open import HLevel
open import Equivalences
open import Equivalence.Alternative
open import Funext
open import HLevelBis


module FiberEquivalences {i j k} {A : Set i} {P : A → Set k} {Q : A → Set j}
  (f : (x : A) → (P x → Q x)) where

-- We want to prove that if [f] induces an equivalence on the total spaces,
-- then [f] induces an equivalence fiberwise

total-map : Σ A P → Σ A Q
total-map (x , y) = (x , f x y)

module TotalMapEquiv (e : is-equiv total-map) where

  total-equiv : Σ A P ≃ Σ A Q
  total-equiv = (total-map , e)

  -- The inverse is propositionally fiberwise
  base-path-inverse : (x : A) (y : Q x) → π₁ ((total-equiv ⁻¹) ☆ (x , y)) ≡ x
  base-path-inverse x y = base-path (inverse-right-inverse total-equiv (x , y))

  -- And the action of [total-map] on paths is correct on the base path
  total-map-fiberwise-on-paths : {u v : Σ A P} (p : u ≡ v)
    → base-path (ap total-map p) ≡ base-path p
  total-map-fiberwise-on-paths {u} {.u} refl = refl

  -- Here is the fiberwise inverse, we use the inverse of the total map and
  -- transform it into a fiberwise map using [base-path-inverse]
  inv : ((x : A) → (Q x → P x))
  inv x y = transport P (base-path-inverse x y)
                        (π₂ ((total-equiv ⁻¹) ☆ (x , y)))

  -- We prove that [inv] is a right and left inverse to [f]

  inv-right-inverse : (x : A) (y : Q x) → f x (inv x y) ≡ y
  inv-right-inverse x y =
    app-trans _ _ f (base-path (inverse-right-inverse total-equiv (x , y)))
              (π₂ (inverse (_ , e) (x , y)))
    ∘ fiber-path (inverse-right-inverse total-equiv (x , y))

  inv-left-inverse : (x : A) (y : P x) → inv x (f x y) ≡ y
  inv-left-inverse x y =
    ap (λ u → transport P (base-path (inverse-right-inverse total-equiv
                                                             (x , f x y))) u)
        (lemma2 x y)
    ∘ (! (trans-concat P (base-path (inverse-right-inverse total-equiv
                                                                 (x , f x y)))
                               (! (base-path-inverse x (f x y))) y)
    ∘ ap (λ p → transport P p y)
          (opposite-left-inverse (ap π₁
            (inverse-right-inverse total-equiv (x , f x y))))) where

    lemma1 : (x : A) (y : P x)
      → base-path-inverse x (f x y)
        ≡ base-path (inverse-left-inverse total-equiv (x , y))
    lemma1 x y = ap base-path (inverse-triangle total-equiv (x , y))
                 ∘ total-map-fiberwise-on-paths _

    lemma2 : (x : A) (y : P x)
      → π₂ ((total-equiv ⁻¹) ☆ (x , f x y))
        ≡ transport P (! (base-path-inverse x (f x y))) y
    lemma2 x y = ! (fiber-path (! (inverse-left-inverse total-equiv (x , y))))
      ∘ ap (λ p → transport P p y)
            (ap-opposite π₁ (inverse-left-inverse total-equiv (x , y))
            ∘ ! (ap ! (lemma1 x y)))

  fiberwise-is-equiv : ((x : A) → is-equiv (f x))
  fiberwise-is-equiv x = iso-is-eq (f x) (inv x) (inv-right-inverse x)
                                              (inv-left-inverse x)

fiberwise-is-equiv : is-equiv total-map → ((x : A) → is-equiv (f x))
fiberwise-is-equiv = TotalMapEquiv.fiberwise-is-equiv

-- Now we do the inverse: if a map is locally an equivalence, it is
-- also so globally
private
  hfiber-to-total : (xq : Σ A Q) → hfiber (f (π₁ xq)) (π₂ xq) → hfiber total-map xq
  hfiber-to-total (x , .(f x a)) (a , refl) = (x , a) , refl

  total-to-hfiber : (xq : Σ A Q) → hfiber total-map xq → hfiber (f (π₁ xq)) (π₂ xq)
  total-to-hfiber .(a , f a p) ((a , p) , refl) = p , refl

  hfiber-total-hfiber : (xq : Σ A Q) (a : hfiber total-map xq) → hfiber-to-total xq (total-to-hfiber xq a) ≡ a
  hfiber-total-hfiber .(a , f a p) ((a , p) , refl) = refl

  total-hfiber-total : (xq : Σ A Q) (a : hfiber (f (π₁ xq)) (π₂ xq)) → total-to-hfiber xq (hfiber-to-total xq a) ≡ a
  total-hfiber-total (x , .(f x p)) (p , refl) = refl

hfiber-is-equiv : (x : A) (q : Q x) → is-equiv (hfiber-to-total (x , q))
hfiber-is-equiv x q = quasinv-is-equiv (hfiber-to-total (x , q)) (make-quasinv (total-to-hfiber (x , q)) (funext (total-hfiber-total (x , q))) (funext (hfiber-total-hfiber (x , q))))

hfiber-equiv : (x : A) (q : Q x) → hfiber (f x) q ≃ hfiber total-map (x , q)
hfiber-equiv x q = hfiber-to-total (x , q) , hfiber-is-equiv x q

equiv-is-fiberwise : ((x : A) → is-equiv (f x)) → is-equiv total-map
equiv-is-fiberwise F (x , q) = equiv-types-truncated ⟨-2⟩ (hfiber-equiv x q) (F x q)

equiv-from-fiberwise : ((x : A) → is-equiv (f x)) → Σ A P ≃ Σ A Q
equiv-from-fiberwise F = total-map , equiv-is-fiberwise F
