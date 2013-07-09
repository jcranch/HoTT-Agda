{-# OPTIONS --without-K #-}

module Types.Sum where

open import Base
open import Equivalence.Alternative
open import HLevelFun



module _ {i j} {A : Set i} {B : Set j} where

  ⊔-empty-l : ¬ B → (A ⊔ B) ≃ A
  ⊔-empty-l nB = f , c where
    f : A ⊔ B → A
    f (inl x) = x
    f (inr x) = abort-nondep (nB x)
    c : (y : A) → is-contr (hfiber f y)
    c y = (inl y , refl) , g where
      g : (r : hfiber f y) → r ≡ inl y , refl
      g (inl .y , refl) = refl
      g (inr x , p) = abort-nondep (nB x)

  ⊔-empty-r : ¬ A → (A ⊔ B) ≃ B
  ⊔-empty-r nA = f , c where
    f : A ⊔ B → B
    f (inl x) = abort-nondep (nA x)
    f (inr x) = x
    c : (y : B) → is-contr (hfiber f y)
    c y = (inr y , refl) , g where
      g : (r : hfiber f y) → r ≡ inr y , refl
      g (inl x , p) = abort-nondep (nA x)
      g (inr .y , refl) = refl


  private
    -- using these merely saves giving a few implicit arguments
    L = inl {A = A} {B = B}
    R = inr {A = A} {B = B}

    ⊔-code-l : A → A ⊔ B → Set i
    ⊔-code-l x₀ (inl x) = x₀ ≡ x
    ⊔-code-l x₀ (inr y) = ⊥

    ⊔-encode-l : (a : A) (x : A ⊔ B) → inl a ≡ x → ⊔-code-l a x
    ⊔-encode-l a x e = transport (⊔-code-l a) e refl

    ⊔-decode-l : (a : A) (x : A ⊔ B) → ⊔-code-l a x → inl a ≡ x
    ⊔-decode-l a (inl x) c = ap inl c
    ⊔-decode-l a (inr x) c = abort c

    ⊔-decode-encode-l : (a : A) (x : A ⊔ B) (e : inl a ≡ x) → ⊔-decode-l a x (⊔-encode-l a x e) ≡ e
    ⊔-decode-encode-l a .(inl a) refl = refl

    ⊔-encode-decode-l : (a : A) (x : A ⊔ B) (c : ⊔-code-l a x) → ⊔-encode-l a x (⊔-decode-l a x c) ≡ c
    ⊔-encode-decode-l .x (inl x) refl = refl
    ⊔-encode-decode-l a (inr x) c = abort-nondep c

    ⊔-code-equiv-l : (a : A) (x : A ⊔ B) → (inl a ≡ x) ≃ ⊔-code-l a x
    ⊔-code-equiv-l a x = (⊔-encode-l a x) , (quasinv-is-equiv (⊔-encode-l a x) (make-quasinv (⊔-decode-l a x) (funext (⊔-decode-encode-l a x)) (funext (⊔-encode-decode-l a x))))

    ⊔-code-r : B → A ⊔ B → Set j
    ⊔-code-r y₀ (inl x) = ⊥
    ⊔-code-r y₀ (inr y) = y₀ ≡ y

    ⊔-encode-r : (b : B) (x : A ⊔ B) → inr b ≡ x → ⊔-code-r b x
    ⊔-encode-r b x e = transport (⊔-code-r b) e refl

    ⊔-decode-r : (b : B) (x : A ⊔ B) → ⊔-code-r b x → inr b ≡ x
    ⊔-decode-r b (inl x) c = abort c
    ⊔-decode-r b (inr x) c = ap inr c

    ⊔-decode-encode-r : (b : B) (x : A ⊔ B) (e : inr b ≡ x) → ⊔-decode-r b x (⊔-encode-r b x e) ≡ e
    ⊔-decode-encode-r b .(inr b) refl = refl

    ⊔-encode-decode-r : (b : B) (x : A ⊔ B) (c : ⊔-code-r b x) → ⊔-encode-r b x (⊔-decode-r b x c) ≡ c
    ⊔-encode-decode-r b (inl x) c = abort-nondep c
    ⊔-encode-decode-r .x (inr x) refl = refl

    ⊔-code-equiv-r : (b : B) (x : A ⊔ B) → (inr b ≡ x) ≃ ⊔-code-r b x
    ⊔-code-equiv-r b x = (⊔-encode-r b x) , (quasinv-is-equiv (⊔-encode-r b x) (make-quasinv (⊔-decode-r b x) (funext (⊔-decode-encode-r b x)) (funext (⊔-encode-decode-r b x))))


    distinguish-⊔ : A ⊔ B → Set zero
    distinguish-⊔ (inl x) = ⊤
    distinguish-⊔ (inr x) = ⊥


  inl≢inr : (a : A) (b : B) → L a ≢ R b 
  inl≢inr a b e = transport distinguish-⊔ e tt


  inl-injective : {a₁ a₂ : A} → L a₁ ≡ L a₂ → a₁ ≡ a₂
  inl-injective {a₁} {a₂} e = transport (⊔-code-l a₁) e refl

  inl-local-equiv : {a₁ a₂ : A} → (L a₁ ≡ L a₂) ≃ (a₁ ≡ a₂)
  inl-local-equiv {a₁} {a₂} = ⊔-code-equiv-l a₁ (inl a₂)


  inr-injective : {b₁ b₂ : B} → R b₁ ≡ R b₂ → b₁ ≡ b₂
  inr-injective {b₁} {b₂} e = transport (⊔-code-r b₁) e refl

  inr-local-equiv : {b₁ b₂ : B} → (R b₁ ≡ R b₂) ≃ (b₁ ≡ b₂)
  inr-local-equiv {b₁} {b₂} = ⊔-code-equiv-r b₁ (inr b₂)


  ⊔-is-truncated : (n : ℕ₋₂) → is-truncated (S (S n)) A → is-truncated (S (S n)) B → is-truncated (S (S n)) (A ⊔ B)
  ⊔-is-truncated n F G (inl x) (inl y) = equiv-types-truncated (S n) (ap L , inverse-is-equiv inl-local-equiv) (F x y)
  ⊔-is-truncated n F G (inl x) (inr y) = abort-nondep ◯ inl≢inr x y
  ⊔-is-truncated n F G (inr x) (inl y) = abort-nondep ◯ inl≢inr y x ◯ !
  ⊔-is-truncated n F G (inr x) (inr y) = equiv-types-truncated (S n) (ap R , inverse-is-equiv inr-local-equiv) (G x y)

  hfiber-inl-inl : (x : A) → is-contr (hfiber L (L x))
  hfiber-inl-inl x = equiv-types-truncated ⟨-2⟩ (equiv-from-fiberwise (λ _ → ap inl) (λ _ → inverse-is-equiv inl-local-equiv)) (pathto-is-contr x)

  hfiber-inl-inr : (b : B) → is-prop (hfiber L (R b))
  hfiber-inl-inr b (a , e) = abort-nondep (inl≢inr a b e)

  hfiber-inr-inl : (a : A) → is-prop (hfiber R (L a))
  hfiber-inr-inl a (b , e) = abort-nondep (inl≢inr a b (! e))

  hfiber-inr-inr : (x : B) → is-contr (hfiber R (R x))
  hfiber-inr-inr x = equiv-types-truncated ⟨-2⟩ (equiv-from-fiberwise (λ _ → ap inr) (λ _ → inverse-is-equiv inr-local-equiv)) (pathto-is-contr x)


  inl-is-truncated-map : is-truncated-map ⟨-1⟩ L
  inl-is-truncated-map (inl x) = contr-is-prop (hfiber-inl-inl x)
  inl-is-truncated-map (inr x) = hfiber-inl-inr x

  inr-is-truncated-map : is-truncated-map ⟨-1⟩ R
  inr-is-truncated-map (inl x) = hfiber-inr-inl x
  inr-is-truncated-map (inr x) = contr-is-prop (hfiber-inr-inr x)



module _ {i j k : Level} {A : Set i} {B : Set j} {C : Set k} (f : A → C) (g : B → C) where
  ⊔-mapout : A ⊔ B → C
  ⊔-mapout (inl x) = f x
  ⊔-mapout (inr x) = g x

  private
    ⊔-mapout-assemble : (c : C) → hfiber f c ⊔ hfiber g c → hfiber ⊔-mapout c
    ⊔-mapout-assemble c (inl (a , p)) = (inl a) , p
    ⊔-mapout-assemble c (inr (b , p)) = (inr b) , p

    ⊔-mapout-disassemble : (c : C) → hfiber ⊔-mapout c → hfiber f c ⊔ hfiber g c
    ⊔-mapout-disassemble c (inl a , p) = inl (a , p)
    ⊔-mapout-disassemble c (inr b , p) = inr (b , p)

    ⊔-mapout-undis : (c : C) (x : hfiber ⊔-mapout c) → ⊔-mapout-assemble c (⊔-mapout-disassemble c x) ≡ x
    ⊔-mapout-undis c (inl a , p) = refl
    ⊔-mapout-undis c (inr b , p) = refl

    ⊔-mapout-disas : (c : C) (x : hfiber f c ⊔ hfiber g c) → ⊔-mapout-disassemble c (⊔-mapout-assemble c x) ≡ x
    ⊔-mapout-disas c (inl (a , p)) = refl
    ⊔-mapout-disas c (inr (b , p)) = refl

  ⊔-mapout-hfiber : (c : C) → hfiber f c ⊔ hfiber g c ≃ hfiber ⊔-mapout c
  ⊔-mapout-hfiber c = ⊔-mapout-assemble c , quasinv-is-equiv (⊔-mapout-assemble c) (make-quasinv (⊔-mapout-disassemble c) (funext (⊔-mapout-disas c)) (funext (⊔-mapout-undis c)))

  ⊔-mapout-truncated : (n : ℕ₋₂) → is-truncated-map (S (S n)) f → is-truncated-map (S (S n)) g → is-truncated-map (S (S n)) ⊔-mapout
  ⊔-mapout-truncated n F G c = equiv-types-truncated (S (S n)) (⊔-mapout-hfiber c) (⊔-is-truncated n (F c) (G c))



module _ {i₁ i₂ j₁ j₂ : Level} {A₁ : Set i₁} {A₂ : Set i₂} {B₁ : Set j₁} {B₂ : Set j₂}
         (f : A₁ → B₁) (g : A₂ → B₂) where
  ⊔-funct : A₁ ⊔ A₂ → B₁ ⊔ B₂
  ⊔-funct = ⊔-mapout (inl ◯ f) (inr ◯ g)

  private
    ⊔-funct-hfiber-l : (x : B₁) → hfiber f x ≃ hfiber ⊔-funct (inl x)
    ⊔-funct-hfiber-l x = equiv-compose (equiv-compose (equiv-compose α (β ⁻¹)) (γ ⁻¹)) δ where
      α : hfiber f x ≃ Σ (hfiber inl (inl x)) (hfiber f ◯ π₁)
      α = fiber-over-contr (hfiber f ◯ π₁) (change-contr-basepoint (x , refl) (hfiber-inl-inl x))
      β : hfiber (inl ◯ f) (inl x) ≃ Σ (hfiber inl (inl x)) (hfiber f ◯ π₁)
      β = hfiber-iter-equiv inl f (inl x)
      γ : hfiber (inl ◯ f) (inl x) ⊔ hfiber (inr ◯ g) (inl x) ≃ hfiber (inl ◯ f) (inl x)
      γ = ⊔-empty-l κ where
        κ : hfiber (inr ◯ g) (inl x) → ⊥
        κ (a , p) = inl≢inr x (g a) (! p)
      δ : hfiber (inl ◯ f) (inl x) ⊔ hfiber (inr ◯ g) (inl x) ≃ hfiber ⊔-funct (inl x)
      δ = ⊔-mapout-hfiber (inl ◯ f) (inr ◯ g) (inl x)

    ⊔-funct-hfiber-r : (x : B₂) → hfiber g x ≃ hfiber ⊔-funct (inr x)
    ⊔-funct-hfiber-r x = equiv-compose (equiv-compose (equiv-compose α (β ⁻¹)) (γ ⁻¹)) δ where
      α : hfiber g x ≃ Σ (hfiber inr (inr x)) (hfiber g ◯ π₁)
      α = fiber-over-contr (hfiber g ◯ π₁) (change-contr-basepoint (x , refl) (hfiber-inr-inr x))
      β : hfiber (inr ◯ g) (inr x) ≃ Σ (hfiber inr (inr x)) (hfiber g ◯ π₁)
      β = hfiber-iter-equiv inr g (inr x)
      γ : hfiber (inl ◯ f) (inr x) ⊔ hfiber (inr ◯ g) (inr x) ≃ hfiber (inr ◯ g) (inr x)
      γ = ⊔-empty-r κ where
        κ : hfiber (inl ◯ f) (inr x) → ⊥
        κ (a , p) = inl≢inr (f a) x p
      δ : hfiber (inl ◯ f) (inr x) ⊔ hfiber (inr ◯ g) (inr x) ≃ hfiber ⊔-funct (inr x)
      δ = ⊔-mapout-hfiber (inl ◯ f) (inr ◯ g) (inr x)

  -- the truncation of ⊔-funct depends only on the truncation of the two parts
  ⊔-funct-truncated : (n : ℕ₋₂) → is-truncated-map n f → is-truncated-map n g → is-truncated-map n ⊔-funct
  ⊔-funct-truncated n F G (inl x) = equiv-types-truncated n (⊔-funct-hfiber-l x) (F x)
  ⊔-funct-truncated n F G (inr x) = equiv-types-truncated n (⊔-funct-hfiber-r x) (G x)

  ⊔-funct-truncated-l : (n : ℕ₋₂) → is-truncated-map n ⊔-funct → is-truncated-map n f
  ⊔-funct-truncated-l n E x = equiv-types-truncated n (⊔-funct-hfiber-l x ⁻¹) (E (inl x))

  ⊔-funct-truncated-r : (n : ℕ₋₂) → is-truncated-map n ⊔-funct → is-truncated-map n g
  ⊔-funct-truncated-r n E x = equiv-types-truncated n (⊔-funct-hfiber-r x ⁻¹) (E (inr x))

module _ {i₁ i₂ j₁ j₂ : Level} {A₁ : Set i₁} {A₂ : Set i₂} {B₁ : Set j₁} {B₂ : Set j₂} where
  private
    U : (A₁ → B₁) × (A₂ → B₂) → (A₁ ⊔ A₂ → B₁ ⊔ B₂)
    U = uncurry (⊔-funct {i₁} {i₂} {j₁} {j₂} {A₁} {A₂} {B₁} {B₂})

{-
    ⊔-funct-preimages : (T : A₁ ⊔ A₂ → B₁ ⊔ B₂) → has-all-paths (hfiber U T)
    ⊔-funct-preimages .(⊔-funct g₁ g₂) ((f₁ , f₂) , a) ((g₁ , g₂) , refl) = Σ-eq (ap₂ _,_ e₁ e₂) {!!} where
      e₁ : f₁ ≡ g₁
      e₁ = funext (inl-injective ◯ happly a ◯ inl)
      e₂ : f₂ ≡ g₂
      e₂ = funext (inr-injective ◯ happly a ◯ inr)

  ⊔-funct-components : is-truncated-map ⟨-1⟩ U
  ⊔-funct-components T = all-paths-is-prop (⊔-funct-preimages T)
-}

-- I'm pretty sure it should be possible to prove this (maybe as
-- above, maybe in such a way as to make more use of path induction),
-- but for now we leave it as a postulate.
  postulate
    ⊔-funct-components : is-truncated-map ⟨-1⟩ U
    