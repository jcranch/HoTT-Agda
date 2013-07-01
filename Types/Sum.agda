module Extra.Sum where

open import Base


⊔-funct : {i₁ i₂ j₁ j₂ : Level} {A₁ : Set i₁} {A₂ : Set i₂} {B₁ : Set j₁} {B₂ : Set j₂} → (A₁ → B₁) → (A₂ → B₂) → A₁ ⊔ A₂ → B₁ ⊔ B₂
⊔-funct f g (inl x) = inl (f x)
⊔-funct f g (inr x) = inr (g x)

⊔-mapout : {i j k : Level} {A : Set i} {B : Set j} {C : Set k} → (A → C) → (B → C) → A ⊔ B → C
⊔-mapout f g (inl x) = f x
⊔-mapout f g (inr x) = g x