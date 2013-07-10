{-# OPTIONS --without-K #-}

module Categories.index where

-- We implement categories as n-full subcategories of spaces for
-- various n. Most things seem to be included in this notion. :-)


open import Categories.Cat0 public
open import Categories.Cat1 public
open import Categories.Cat2 public
open import Categories.Cat3 public

open import Categories.Cat0to1 public
open import Categories.Cat1to2 public

open import Categories.Cat1.ProductCat public
open import Categories.Cat1.UnionCat public

open import Categories.Examples.AKS
open import Categories.Examples.Delta
open import Categories.Examples.Groupoids
open import Categories.Examples.Sets

open import Categories.Counterexamples.Cat0