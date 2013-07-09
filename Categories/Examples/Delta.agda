{-# OPTIONS --without-K #-}

module Categories.Examples.Delta where

open import Base
open import HLevelFun

open import Categories.Cat1
open import Types.Sum



data Fin : ℕ → Set where
  fzero : (n : ℕ) → Fin (S n)
  fsuc : {n : ℕ} → Fin n → Fin (S n)

private
  distinguish-fzero : {n : ℕ} → Fin n → Set zero
  distinguish-fzero (fzero n) = ⊥
  distinguish-fzero (fsuc a) = ⊤

  unfsuc : {n : ℕ} → Fin (S (S n)) → Fin (S n)
  unfsuc {n} (fzero .(S n)) = fzero n
  unfsuc (fsuc a) = a

fzero≢fsuc : {n : ℕ} {a : Fin n} → fzero n ≢ fsuc a
fzero≢fsuc e = transport distinguish-fzero (! e) tt

suc-inj : {n : ℕ} {a b : Fin n} → fsuc a ≡ fsuc b → a ≡ b
suc-inj {O} {}
suc-inj {S n} = ap unfsuc

private
  fsuc-neq : {n : ℕ} {a b : Fin n} → (a ≡ b → ⊥) → (fsuc a ≡ fsuc b → ⊥ {zero})
  fsuc-neq e = e ◯ suc-inj

fin-has-dec-eq : (n : ℕ) → has-dec-eq (Fin n)
fin-has-dec-eq O () _
fin-has-dec-eq (S n) (fzero .n) (fzero .n) = inl refl
fin-has-dec-eq (S n) (fzero .n) (fsuc b) = inr fzero≢fsuc
fin-has-dec-eq (S n) (fsuc a) (fzero .n) = inr (fzero≢fsuc ◯ !)
fin-has-dec-eq (S n) (fsuc a) (fsuc b) = ⊔-funct (ap fsuc) fsuc-neq (fin-has-dec-eq n a b)

fin-is-set : (n : ℕ) → is-set (Fin n)
fin-is-set n = dec-eq-is-set (fin-has-dec-eq n)



-- ozero is the map with empty domain
-- osucʳ says "increment the values"
-- osucˡ says "increment the domain, and send 0 to 0"
data Ord : ℕ → ℕ → Set where
  ozero : Ord O O
  osucʳ : {m n : ℕ} → Ord m n → Ord m (S n)
  osucˡ : {m n : ℕ} → Ord m (S n) → Ord (S m) (S n)

private
  distinguish-osucs : {m n : ℕ} (f : Ord m n) → Set zero
  distinguish-osucs ozero = ⊥
  distinguish-osucs (osucʳ f) = ⊥
  distinguish-osucs (osucˡ f) = ⊤

  unosucˡ : {m n : ℕ} → Ord (S m) n → Ord m n
  unosucˡ {m} {S n} (osucʳ f) = osucʳ (unosucˡ f)
  unosucˡ (osucˡ f) = f

  unosucʳ : {m n : ℕ} → Ord m (S (S n)) → Ord m (S n)
  unosucʳ {m} {n} (osucʳ f) = f
  unosucʳ {S m} {n} (osucˡ f) = osucˡ (unosucʳ f)

osucˡ≠osucʳ : {m n : ℕ} (f : Ord m (S n)) (g : Ord (S m) n) → osucˡ f ≢ osucʳ g
osucˡ≠osucʳ {m} {n} f g e = transport distinguish-osucs e tt

osucˡ-inj : {m n : ℕ} (f g : Ord m (S n)) → osucˡ f ≡ osucˡ g → f ≡ g
osucˡ-inj {m} {n} f g = ap unosucˡ

osucʳ-inj : {m n : ℕ} (f g : Ord m n) → osucʳ f ≡ osucʳ g → f ≡ g
osucʳ-inj {.0} {O} ozero ozero e = refl
osucʳ-inj {m} {S n} f g e = ap unosucʳ e

private
  osucˡ-neq : {m n : ℕ} (f g : Ord m (S n)) → f ≢ g → osucˡ f ≢ osucˡ g
  osucˡ-neq f g e = e ◯ osucˡ-inj f g

  osucʳ-neq : {m n : ℕ} (f g : Ord m n) → f ≢ g → osucʳ f ≢ osucʳ g
  osucʳ-neq f g e = e ◯ osucʳ-inj f g

ord-has-dec-eq : (m n : ℕ) → has-dec-eq (Ord m n)
ord-has-dec-eq .0 .0 ozero ozero = inl refl
ord-has-dec-eq m (S n) (osucʳ f) (osucʳ g) = ⊔-funct (ap osucʳ) (osucʳ-neq f g) (ord-has-dec-eq m n f g)
ord-has-dec-eq (S m) (S n) (osucʳ f) (osucˡ g) = inr (osucˡ≠osucʳ g f ◯ !)
ord-has-dec-eq (S m) (S n) (osucˡ f) (osucʳ g) = inr (osucˡ≠osucʳ f g)
ord-has-dec-eq (S m) (S n) (osucˡ f) (osucˡ g) = ⊔-funct (ap osucˡ) (osucˡ-neq f g) (ord-has-dec-eq m (S n) f g)

ord-is-set : (m n : ℕ) → is-set (Ord m n)
ord-is-set m n = dec-eq-is-set (ord-has-dec-eq m n)



ord-map : {m n : ℕ} → Ord m n → Fin m → Fin n
ord-map ozero ()
ord-map (osucʳ f) x = fsuc (ord-map f x)
ord-map (osucˡ {m} {n} f) (fzero .m) = fzero n
ord-map (osucˡ f) (fsuc x) = ord-map f x



ord-id : (m : ℕ) → Ord m m
ord-id O = ozero
ord-id (S m) = osucˡ (osucʳ (ord-id m))

ord-id-is-id : {m : ℕ} (x : Fin m) → ord-map (ord-id m) x ≡ x
ord-id-is-id (fzero n) = refl
ord-id-is-id (fsuc x) = ap fsuc (ord-id-is-id x)



ord-compose : {m n o : ℕ} → Ord n o → Ord m n → Ord m o
ord-compose ozero ozero = ozero
ord-compose (osucʳ g) f = osucʳ (ord-compose g f)
ord-compose (osucˡ g) (osucʳ f) = ord-compose g f
ord-compose (osucˡ g) (osucˡ f) = osucˡ (ord-compose (osucˡ g) f)

ord-compose-is-cmp : {m n o : ℕ} (g : Ord n o) (f : Ord m n) (x : Fin m) → ord-map (ord-compose g f) x ≡ ord-map g (ord-map f x)
ord-compose-is-cmp ozero ozero ()
ord-compose-is-cmp (osucʳ g) f x = ap fsuc (ord-compose-is-cmp g f x)
ord-compose-is-cmp (osucˡ g) (osucʳ f) x = ord-compose-is-cmp g f x
ord-compose-is-cmp (osucˡ {n} {o} g) (osucˡ {m} f) (fzero .m) = refl
ord-compose-is-cmp (osucˡ g) (osucˡ f) (fsuc x) = ord-compose-is-cmp (osucˡ g) f x



ord-eq : {m n : ℕ} (f g : Ord m n) → ((x : Fin m) → ord-map f x ≡ ord-map g x) → f ≡ g
ord-eq ozero ozero ε = refl
ord-eq {.0} {S O} (osucʳ ozero) (osucʳ ozero) ε = refl
ord-eq {m} {S (S n)} (osucʳ f) (osucʳ g) ε = ap osucʳ (ord-eq f g (ap unfsuc ◯ ε))
ord-eq (osucʳ f) (osucˡ g) ε = abort-nondep (fzero≢fsuc (! (ε (fzero _))))
ord-eq (osucˡ f) (osucʳ g) ε = abort-nondep (fzero≢fsuc (ε (fzero _)))
ord-eq (osucˡ f) (osucˡ g) ε = ap osucˡ (ord-eq f g (ε ◯ fsuc))

ord-eq′ : {m n : ℕ} {f g : Ord m n} → ord-map f ≡ ord-map g → f ≡ g
ord-eq′ {m} {n} {f} {g} e = ord-eq f g (happly e)



ordFib : {m n : ℕ} (f : Fin m → Fin n) → is-prop (hfiber ord-map f)
ordFib {m} {n} f = injection-to-set ord-map (→-is-truncated ⟨0⟩ (fin-is-set n)) ord-eq′ f



Delta : Concrete₁
Delta = record {
          obj = ℕ;
          obj⁺ = Fin;
          hom = Ord;
          hom⁺ = ord-map;
          conf = ordFib;
          ident′ = λ x → ord-id x , funext ord-id-is-id;
          cmp′ = λ g f → ord-compose g f , funext (ord-compose-is-cmp g f) }
