{-# OPTIONS --without-K #-}

module Equivalence.HalfAdjoint where

open import Base


module _ {i j} {A : Set i} {B : Set j} (f : A → B) where


  haeˡ-is-prop : is-prop haeˡ
  haeˡ-is-prop = {!!}

  haeʳ-is-prop : is-prop haeʳ
  haeʳ-is-prop = {!!}

  equiv→haeˡ : is-equiv f → haeˡ
  equiv→haeˡ e = {!!}

  haeˡ→equiv : haeˡ → is-equiv f
  haeˡ→equiv h = {!!}

  haeˡ→haeʳ : haeˡ → haeʳ
  haeˡ→haeʳ (make-haeˡ g η ε τ) = make-haeʳ g η ε {!!}

  haeʳ→haeˡ : haeʳ → haeˡ
  haeʳ→haeˡ (make-haeʳ g η ε ν) = make-haeˡ g η ε {!!}
{-
  haeˡ-equiv

  haeʳ-equiv
-}