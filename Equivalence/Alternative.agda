{-# OPTIONS --without-K #-}

module Equivalence.Alternative where

-- Five different notions:
--   1. equivalence,
--   2. left half-adjoint equivalence,
--   3. right half-adjoint equivalence,
--   4. bi-invertibility,
--   5. quasi-invertibility
--
-- We produce maps as follows:
--   2 → 1,
--   5 → 2,
--   5 → 4,
--   1 → 5,  2 → 5,  3 → 5,  4 → 5,
-- and hence prove equivalence of all notions but 3.


open import Base



module _ {i j} {A : Set i} {B : Set j} (f : A → B) where


  record is-halfadjˡ : Set (max i j) where
    constructor make-halfadjˡ
    field
      g : B → A
      η : g ◯ f ≡ id A
      ε : f ◯ g ≡ id B
      τ : ap f ◯ happly η ≡ happly ε ◯ f

  record is-halfadjʳ : Set (max i j) where
    constructor make-halfadjʳ
    field
      g : B → A
      η : g ◯ f ≡ id A
      ε : f ◯ g ≡ id B
      ν : ap g ◯ happly ε ≡ happly η ◯ g


  record is-quasinv : Set (max i j) where
    constructor make-quasinv
    field
      g : B → A
      η : g ◯ f ≡ id A
      ε : f ◯ g ≡ id B


  is-left-invertible : Set (max i j)
  is-left-invertible = Σ (B → A) (λ g → g ◯ f ≡ id A)

  is-right-invertible : Set (max i j)
  is-right-invertible = Σ (B → A) (λ g → f ◯ g ≡ id B)

  is-bi-invertible : Set (max i j)
  is-bi-invertible = is-left-invertible × is-right-invertible


  equiv-is-quasinv : is-equiv f → is-quasinv
  equiv-is-quasinv e = make-quasinv (inverse (f , e)) (funext (inverse-left-inverse (f , e))) (funext (inverse-right-inverse (f , e)))

  halfadjˡ-is-quasinv : is-halfadjˡ → is-quasinv
  halfadjˡ-is-quasinv (make-halfadjˡ g η ε τ) = make-quasinv g η ε

  halfadjʳ-is-quasinv : is-halfadjʳ → is-quasinv
  halfadjʳ-is-quasinv (make-halfadjʳ g η ε ν) = make-quasinv g η ε

  biinv-is-quasinv : is-bi-invertible → is-quasinv
  biinv-is-quasinv ((g , η) , (g′ , ε)) = make-quasinv g η ε′ where
    -- f ◯ g ≡ f ◯ g ◯ f ◯ g′ ≡ f ◯ g′ ≡ 1
    ε′ : f ◯ g ≡ id B
    ε′ = ap (λ k → f ◯ g ◯ k) (! ε) ∘ ap (λ k → f ◯ k ◯ g′) η ∘ ε

  quasinv-is-biinv : is-quasinv → is-bi-invertible
  quasinv-is-biinv (make-quasinv g η ε) = (g , η) , (g , ε)

  halfadjˡ-is-equiv : is-halfadjˡ → is-equiv f
  halfadjˡ-is-equiv (make-halfadjˡ g η ε τ) y = (g y , happly ε y) , P where
    P : (p : hfiber f y) → p ≡ g y , happly ε y
    P (x , e) = Σ-eq a (trans-app≡cst f y a e ∘ b) where
      a : x ≡ g y
      a = ! (happly η x) ∘ (ap g e)
      b : ! (ap f (! (happly η x) ∘ ap g e)) ∘ e ≡ happly ε y
      b = ap (λ z → ! z ∘ e) (ap-concat f (! (happly η x)) (ap g e) ∘ ap (λ z → z ∘ ap f (ap g e)) (ap-opposite f (happly η x))) ∘ ap (λ z → z ∘ e) (opposite-concat (! (ap f (happly η x))) (ap f (ap g e))) ∘ ap (λ z → (! (ap f (ap g e)) ∘ z) ∘ e) (opposite-opposite (ap f (happly η x)) ∘ happly τ x) ∘ ap (λ z → (! (ap f (ap g e)) ∘ happly ε (f x)) ∘ z) (! (ap-id (! (! e)) ∘ opposite-opposite e)) ∘ concat-assoc (! (ap f (ap g e))) (happly ε (f x)) (ap (id _) (! (! e))) ∘ ap (λ z → z ∘ happly ε (f x) ∘ ap (id _) (! (! e))) (ap ! (compose-ap f g e) ∘ opposite-ap (f ◯ g) e) ∘ happly-natural′ ε (! e)

  -- HoTT book, p126
  quasinv-is-halfadjˡ : is-quasinv → is-halfadjˡ
  quasinv-is-halfadjˡ (make-quasinv g η ε) = make-halfadjˡ g η ε′ τ where

    -- ε′ : f ◯ g ≡ f ◯ g ◯ f ◯ g ≡ f ◯ g ≡ id B 
    ε′ : f ◯ g ≡ id B
    ε′ = ap (λ k → f ◯ g ◯ k) (! ε) ∘ (ap (λ k → f ◯ k ◯ g) η ∘ ε)

  -- Once the inverse is moved to the other side, the goal is approximately:
  --   ap (f ◯ g) (happly ε (f x)) ∘ ap f (happly η x) ≡ ap f (happly η (g (f x))) ∘ happly ε (f x)
  -- There are then basically two ingredients in the proof
  -- 1. happly-natural ε (ap f (happly η x))
  -- 2. (ap (ap f) (happly-id-natural η x)), and similarly, happly-id-natural ε (f x))
  -- All the rest is rather unpleasant standard manipulations.
    τ : ap f ◯ happly η ≡ happly ε′ ◯ f
    τ = funext T where
      T : (x : A) → ap f (happly η x) ≡ happly ε′ (f x)
      T x = move!-left-on-left (ap f (ap (λ u → u x) η)) (ap (λ k → k (f x)) (ap (λ k z → f (g (k z))) ε)) (ap (λ k → k (f x)) (ap (λ k x₁ → f (k (g x₁))) η ∘ ε)) (ap (λ z → z ∘ ap f (happly η x)) (compose-ap (λ k → k (f x))  (λ k z → f (g (k z))) ε) ∘ ap₂ _∘_ {ap (λ x₁ → f (g (x₁ (f x)))) ε} {ap (λ u → u (f (g (f x)))) ε} {ap f (ap (λ u → u x) η)} {ap (λ x₁ → x₁) (ap f (ap (λ u → u x) η))} (ap-compose (f ◯ g) (λ k → k (f x)) ε ∘ ! (happly-id-natural ε (f x))) (! (ap-id (ap f (happly η x)))) ∘ ! (happly-natural ε (ap f (happly η x))) ∘ ap (λ z → z ∘ happly ε (f x)) {ap (λ y → f (g y)) (ap f (ap (λ k → k x) η))} {ap (λ k → k (f x)) (ap (λ k y → f (k (g y))) η)} (compose-ap (f ◯ g) f (happly η x) ∘ ap-compose f (g ◯ f) (happly η x) ∘ ! (ap (ap f) (happly-id-natural η x)) ∘ compose-ap f (λ u → u (g (f x))) η ∘ ap-compose (λ k → k (f x)) (λ k y → f (k (g y))) η) ∘ concat-ap (λ k → k (f x)) (ap (λ k y → f (k (g y))) η) ε) ∘ ap (λ z → z ∘ ap (λ k → k (f x)) (ap (λ k x₁ → f (k (g x₁))) η ∘ ε)) (opposite-ap (λ k → k (f x)) (ap (λ k z → f (g (k z))) ε) ∘ ap (ap (λ k → k (f x))) (opposite-ap (λ k z → f (g (k z))) ε)) ∘ concat-ap (λ k → k (f x)) (ap (λ k → f ◯ g ◯ k) (! ε)) (ap (λ k → f ◯ k ◯ g) η ∘ ε)

  quasinv-is-equiv : is-quasinv → is-equiv f
  quasinv-is-equiv = halfadjˡ-is-equiv ◯ quasinv-is-halfadjˡ

  biinv-is-equiv : is-bi-invertible → is-equiv f
  biinv-is-equiv = halfadjˡ-is-equiv ◯ quasinv-is-halfadjˡ ◯ biinv-is-quasinv

  equiv-is-biinv : is-equiv f → is-bi-invertible
  equiv-is-biinv = quasinv-is-biinv ◯ equiv-is-quasinv

  equiv-is-halfadjˡ : is-equiv f → is-halfadjˡ
  equiv-is-halfadjˡ = quasinv-is-halfadjˡ ◯ equiv-is-quasinv

  halfadjˡ-is-biinv : is-halfadjˡ → is-bi-invertible
  halfadjˡ-is-biinv = quasinv-is-biinv ◯ halfadjˡ-is-quasinv

  biinv-is-halfadjˡ : is-bi-invertible → is-halfadjˡ
  biinv-is-halfadjˡ = quasinv-is-halfadjˡ ◯ biinv-is-quasinv



module _ {i j} {A : Set i} {B : Set j} (f : A → B) where

  quasinv-inverse : (i : is-quasinv f) → is-quasinv (is-quasinv.g f i)
  quasinv-inverse (make-quasinv g η ε) = make-quasinv f ε η

  halfadjˡ-inverse : (h : is-halfadjˡ f) → is-halfadjʳ (is-halfadjˡ.g f h)
  halfadjˡ-inverse (make-halfadjˡ g η ε τ) = make-halfadjʳ f ε η τ

  halfadjʳ-inverse : (h : is-halfadjʳ f) → is-halfadjˡ (is-halfadjʳ.g f h)
  halfadjʳ-inverse (make-halfadjʳ g η ε ν) = make-halfadjˡ f ε η ν



{-
-- A to-do list:


  left-invertible-is-prop : is-right-invertible → is-prop is-left-invertible
  left-invertible-is-prop (g , e) = all-paths-is-prop F where
    F : (a b : is-left-invertible) → a ≡ b
    F (g₁ , e₁) (g₂ , e₂) = Σ-eq (funext (λ x → ap g₁ (! (happly e x)) ∘ happly (e₁ ∘ ! e₂) (g x) ∘ ap g₂ (happly e x))) {!!}

  right-invertible-is-prop : is-left-invertible → is-prop is-right-invertible
  right-invertible-is-prop (g , e) = all-paths-is-prop F where
    F : (a b : is-right-invertible) → a ≡ b
    F (g₁ , e₁) (g₂ , e₂) = Σ-eq (funext (λ x → ! (happly e (g₁ x)) ∘ ap g ((happly e₁ x) ∘ ! (happly e₂ x)) ∘ happly e (g₂ x))) {!!}

  biinv-is-prop : is-prop is-bi-invertible
  biinv-is-prop = inhab→prop-is-prop c where
    c : is-bi-invertible → is-prop is-bi-invertible
    c (l , r) = ×-is-truncated ⟨-1⟩ (left-invertible-is-prop r) (right-invertible-is-prop l)



  halfadjˡ-is-prop : is-prop is-halfadjˡ
  halfadjˡ-is-prop = {!!}



-- Two propositions are equivalent if they imply each other
biimplication-is-equiv : ∀ {i j} {A : Set i} {B : Set j} → is-prop A → is-prop B → (f : A → B) → (B → A) → is-equiv f
biimplication-is-equiv p q f g = quasinv-is-equiv f (make-quasinv g (funext (λ x → prop-has-all-paths p (g (f x)) x)) (funext (λ x → prop-has-all-paths q (f (g x)) x)))

biimplication-equiv : ∀ {i j} {A : Set i} {B : Set j} → is-prop A → is-prop B → (f : A → B) → (B → A) → A ≃ B
biimplication-equiv p q f g = f , biimplication-is-equiv p q f g



module _ {i j} {A : Set i} {B : Set j} (f : A → B) where

  halfadjˡ≃biinv : is-halfadjˡ f ≃ is-bi-invertible f
  halfadjˡ≃biinv = biimplication-equiv (halfadjˡ-is-prop f) (biinv-is-prop f) (halfadjˡ-is-biinv f) (biinv-is-halfadjˡ f)

  biinv≃equiv : is-bi-invertible f ≃ is-equiv f
  biinv≃equiv = biimplication-equiv (biinv-is-prop f) (is-equiv-is-prop f) (biinv-is-equiv f) (equiv-is-biinv f)

  halfadjˡ≃equiv : is-halfadjˡ f ≃ is-equiv f
  halfadjˡ≃equiv = biimplication-equiv (halfadjˡ-is-prop f) (is-equiv-is-prop f) (halfadjˡ-is-equiv f) (equiv-is-halfadjˡ f)

-}