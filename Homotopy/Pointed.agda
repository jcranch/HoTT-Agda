{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Truncation

module Homotopy.Pointed where

Set⋆ : (i : Level) → Set (suc i)
Set⋆ i = Σ (Set i) (id (Set i))

∣_∣ : {i : Level} → Set⋆ i → Set i
∣_∣ = π₁
⋆ : {i : Level} (A : Set⋆ i) → ∣ A ∣
⋆ = π₂

Set⋆₀ : Set₁
Set⋆₀ = Set⋆ zero

_→⋆_ : ∀ {i j} → (Set⋆ i → Set⋆ j → Set⋆ (max i j))
(A , a) →⋆ (B , b) = (Σ (A → B) (λ f → f a ≡ b) , (cst b , refl b))

id⋆ : ∀ {i} (A : Set⋆ i) → ∣ A →⋆ A ∣
id⋆ (A , a) = id A , refl a

cst⋆ : ∀ {i j} (A : Set⋆ i) (B : Set⋆ j) → ∣ A →⋆ B ∣
cst⋆ (A , a) (B , b) = (cst b , refl b)

τ⋆ : ∀ {i} → (ℕ₋₂ → Set⋆ i → Set⋆ i)
τ⋆ n (X , x) = (τ n X , proj x)

is-contr⋆ : ∀ {i} → (Set⋆ i → Set i)
is-contr⋆ (X , x) = is-contr X

_≃⋆_ : ∀ {i j} → (Set⋆ i → Set⋆ j → Set (max i j))
(X , x) ≃⋆ (Y , y) = Σ (X ≃ Y) (λ f → π₁ f x ≡ y)

id-equiv⋆ : ∀ {i} (X : Set⋆ i) → X ≃⋆ X
id-equiv⋆ (X , x) = (id-equiv X , refl x)

equiv-compose⋆ : ∀ {i j k} {A : Set⋆ i} {B : Set⋆ j} {C : Set⋆ k}
  → (A ≃⋆ B → B ≃⋆ C → A ≃⋆ C)
equiv-compose⋆ (f , pf) (g , pg) = (equiv-compose f g , (map (π₁ g) pf ∘ pg))

Set⋆-eq-raw : ∀ {i} {X Y : Set⋆ i} (p : ∣ X ∣ ≡ ∣ Y ∣)
  (q : transport (λ X → X) p (⋆ X) ≡ ⋆ Y) → X ≡ Y
Set⋆-eq-raw {i} {(X , x)} {(.X , .x)} (refl .X) (refl .x) = refl _

Set⋆-eq : ∀ {i} {X Y : Set⋆ i} → (X ≃⋆ Y → X ≡ Y)
Set⋆-eq (e , p) = Set⋆-eq-raw (eq-to-path e) (trans-id-eq-to-path e _ ∘ p)
