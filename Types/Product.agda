{-# OPTIONS --without-K #-}

module Types.Product where

open import Base
open import Equivalence.Alternative
open import HLevelFun


module _ {i₁ i₂ j₁ j₂ : Level} {A₁ : Set i₁} {A₂ : Set i₂} {B₁ : Set j₁} {B₂ : Set j₂} (f : A₁ → B₁) (g : A₂ → B₂) where

  ×-funct : A₁ × A₂ → B₁ × B₂
  ×-funct (x , y) = (f x , g y)

  private
    from-prod : (b₁ : B₁) (b₂ : B₂) → hfiber f b₁ × hfiber g b₂ → hfiber ×-funct (b₁ , b₂)
    from-prod b₁ b₂ ((x₁ , e₁) , (x₂ , e₂)) = (x₁ , x₂) , Σ-eq e₁ (trans-cst e₁ (g x₂) ∘ e₂)

    to-prod : (b₁ : B₁) (b₂ : B₂) → hfiber ×-funct (b₁ , b₂) → hfiber f b₁ × hfiber g b₂
    to-prod b₁ b₂ ((x₁ , x₂) , e) = (x₁ , ap π₁ e) , (x₂ , ap π₂ e)

    from-to : (b : B₁ × B₂) (r : hfiber ×-funct b) → from-prod (π₁ b) (π₂ b) (to-prod (π₁ b) (π₂ b) r) ≡ r
    from-to .(f x₁ , g x₂) ((x₁ , x₂) , refl) = refl

    to-from : (b₁ : B₁) (b₂ : B₂) (r : hfiber f b₁ × hfiber g b₂) → to-prod b₁ b₂ (from-prod b₁ b₂ r) ≡ r
    to-from .(f x₁) .(g x₂) ((x₁ , refl) , (x₂ , refl)) = refl

  ×-funct-hfiber : (b₁ : B₁) (b₂ : B₂) → hfiber f b₁ × hfiber g b₂ ≃ hfiber ×-funct (b₁ , b₂)
  ×-funct-hfiber b₁ b₂ = (from-prod b₁ b₂) , (quasinv-is-equiv (from-prod b₁ b₂) (make-quasinv (to-prod b₁ b₂) (funext (to-from b₁ b₂)) (funext (from-to (b₁ , b₂)))))

  ×-funct-truncated : (n : ℕ₋₂) → is-truncated-map n f → is-truncated-map n g → is-truncated-map n ×-funct
  ×-funct-truncated n F G (b₁ , b₂) = equiv-types-truncated n (×-funct-hfiber b₁ b₂) (×-is-truncated n (F b₁) (G b₂))