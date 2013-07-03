{-# OPTIONS --without-K #-}

module Equivalence.Biinvertible where

open import Base

module _ {i j} {A : Set i} {B : Set j} (f : A → B) where



  equiv-implies-left-invertible : is-equiv f → left-invertible
  equiv-implies-left-invertible e = {!!}

  equiv-implies-right-invertible : is-equiv f → right-invertible
  equiv-implies-right-invertible e = {!!}

  bi-invertible-implies-equiv : bi-invertible → is-equiv f
  bi-invertible-implies-equiv (l , r) = {!!}

  bi-invertible-equiv : bi-invertible ≃ is-equiv f
  bi-invertible-equiv = {!!}




module _ {i j k} {A : Set i} {B : Set j} {C : Set k} (f : A → B) where

  private
    precomp : (C → A) → (C → B)
    precomp k = f ◯ k

    postcomp : (B → C) → (A → C)
    postcomp k = k ◯ f

  left-invertible-precomp : left-invertible f → left-invertible precomp
  left-invertible-precomp (g , e) = (λ k → g ◯ k) , funext (λ k → funext (happly e ◯ k))

  left-invertible-postcomp : right-invertible f → left-invertible postcomp
  left-invertible-postcomp (g , e) = (λ k → k ◯ g) , funext (λ k → funext (ap k ◯ happly e))

  right-invertible-precomp : right-invertible f → right-invertible precomp
  right-invertible-precomp (g , e) = (λ k → g ◯ k) , funext (λ k → funext (happly e ◯ k))

  right-invertible-postcomp : left-invertible f → right-invertible postcomp
  right-invertible-postcomp (g , e) = (λ k → k ◯ g) , funext (λ k → funext (ap k ◯ happly e))

