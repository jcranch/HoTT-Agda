{-# OPTIONS --without-K #-}

open import Base

module Homotopy.Pointed where

open import Integers
open import Homotopy.Truncation
open import Homotopy.Connected

record Set⋆ (i : Level) : Set (suc i) where
  constructor ⋆[_,_]
  field
    ∣_∣ : Set i  -- \|
    ⋆ : ∣_∣  -- \*
open Set⋆ public

Set⋆₀ : Set₁
Set⋆₀ = Set⋆ zero

_⋆→_ : ∀ {i j} → (Set⋆ i → Set⋆ j → Set (max i j))
⋆[ A , a ] ⋆→ ⋆[ B , b ] = Σ (A → B) (λ f → f a ≡ b)

_→⋆_ : ∀ {i j} → (Set⋆ i → Set⋆ j → Set⋆ (max i j))
⋆[ A , a ] →⋆ ⋆[ B , b ] = ⋆[ ⋆[ A , a ] ⋆→ ⋆[ B , b ] , (cst b , refl) ]

id⋆ : ∀ {i} (A : Set⋆ i) → ∣ A →⋆ A ∣
id⋆ ⋆[ A , a ] = id A , refl

cst⋆ : ∀ {i j} (A : Set⋆ i) (B : Set⋆ j) → ∣ A →⋆ B ∣
cst⋆ ⋆[ A , a ] ⋆[ B , b ] = (cst b , refl)

τ⋆ : ∀ {i} → (ℕ₋₂ → Set⋆ i → Set⋆ i)
τ⋆ n ⋆[ X , x ] = ⋆[ τ n X , proj x ]

is-contr⋆ : ∀ {i} → (Set⋆ i → Set i)
is-contr⋆ ⋆[ X , x ] = is-contr X

is-connected⋆ : ∀ {i} → ℕ₋₂ → (Set⋆ i → Set i)
is-connected⋆ n ⋆[ X , x ] = is-connected n X

connected⋆-lt : ∀ {i} (k n : ℕ) (lt : k < S n) (X : Set⋆ i)
  → (is-connected⋆ ⟨ n ⟩ X → is-contr⋆ (τ⋆ ⟨ k ⟩ X))
connected⋆-lt .n n <n X p = p
connected⋆-lt k O (<S ()) X p
connected⋆-lt k (S n) (<S lt) X p =
  connected⋆-lt k n lt X (connected-S-is-connected ⟨ n ⟩ p)

_≃⋆_ : ∀ {i j} → (Set⋆ i → Set⋆ j → Set (max i j))
⋆[ X , x ] ≃⋆ ⋆[ Y , y ] = Σ (X ≃ Y) (λ f → π₁ f x ≡ y)

id-equiv⋆ : ∀ {i} (X : Set⋆ i) → X ≃⋆ X
id-equiv⋆ ⋆[ X , x ] = (id-equiv X , refl)

equiv-compose⋆ : ∀ {i j k} {A : Set⋆ i} {B : Set⋆ j} {C : Set⋆ k}
  → (A ≃⋆ B → B ≃⋆ C → A ≃⋆ C)
equiv-compose⋆ (f , pf) (g , pg) = (equiv-compose f g , (ap (π₁ g) pf ∘ pg))

Set⋆-eq-raw : ∀ {i} {X Y : Set⋆ i} (p : ∣ X ∣ ≡ ∣ Y ∣)
  (q : transport (λ X → X) p (⋆ X) ≡ ⋆ Y) → X ≡ Y
Set⋆-eq-raw {i} {⋆[ X , x ]} {⋆[ .X , .x ]} refl refl = refl

Set⋆-eq : ∀ {i} {X Y : Set⋆ i} → (X ≃⋆ Y → X ≡ Y)
Set⋆-eq (e , p) = Set⋆-eq-raw (eq-to-path e) (trans-id-eq-to-path e _ ∘ p)
