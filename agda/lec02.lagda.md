```agda
{-# OPTIONS --without-K --safe #-}

module lec02 where
open import lec01 hiding (𝟘 ; 𝟙 ; D)

-- Empty type
data 𝟘 : Type where

𝟘-elim : {P : 𝟘 → Type} (x : 𝟘) → P x
𝟘-elim ()

¬_ : Type → Type
¬ A = A → 𝟘
infix 1000 ¬_

𝟘-nondep-elim : {P : Type} → 𝟘 → P
𝟘-nondep-elim {P} = 𝟘-elim {λ _ → P}

is-empty : Type → Type
is-empty A = A → 𝟘

𝟘-is-empty : is-empty 𝟘
𝟘-is-empty = id

-- Unit type using record
-- Record definitions satisfy a certain η rule.
record 𝟙 : Type where
  constructor
    ⋆
open 𝟙 public

𝟙-elim : {P : 𝟙 → Type}
  → P ⋆
  → (x : 𝟙) → P x
𝟙-elim b x = b -- We don't need to pattern match on x because Agda knows that 𝟙 satisfies the η rule

𝟙-nondep-elim : {P : Type}
  → P
  → 𝟙 → P
𝟙-nondep-elim = 𝟙-elim

𝟙-is-nonempty : ¬ is-empty 𝟙
𝟙-is-nonempty f = f ⋆

data 𝟚 : Type where
  𝟎 𝟏 : 𝟚

𝟚-elim : {P : 𝟚 → Type}
  → P 𝟎
  → P 𝟏
  → (x : 𝟚) → P x
𝟚-elim x₀ x₁ 𝟎 = x₀
𝟚-elim x₀ x₁ 𝟏 = x₁

𝟚-nondep-elim : {P : Type}
  → P
  → P
  → 𝟚 → P
𝟚-nondep-elim = 𝟚-elim

Pi : (A : Type) (B : A → Type) → Type
Pi A B = (x : A) → B x

syntax Pi A (λ x → b) = Π x ꞉ A , b

-- Function composition

module _ where private
  _∘_ : {A B C : Type} → (B → C) → (A → B) → (A → C)
  (g ∘ f) x = g (f x)

-- A more general version
_∘_ : {A B : Type} {C : B → Type}
  → (Π b ꞉ B , C b)
  → (f : A → B)
  → Π a ꞉ A , C (f a)
(g ∘ f) x = g (f x)

module _ where private
  data Σ {A : Type} (B : A → Type) : Type where
    _,_ : (x : A) (y : B x) → Σ {A} B

  pr₁ : {A : Type} {B : A → Type} → Σ B → A
  pr₁ (x , y) = x
  pr₂ : {A : Type} {B : A → Type} → (z : Σ B) → B (pr₁ z)
  pr₂ (x , y) = y

-- Alternative definition (using record)

record Σ {A : Type} (B : A → Type) : Type where
  constructor
    _,_
  field
    pr₁ : A
    pr₂ : B pr₁
-- This definition satisfies the η-rule z = (pr₁ z , pr₂ z), the definition using data doesn't

open Σ public
infixr 0 _,_

Sigma : (A : Type) (B : A → Type) → Type
Sigma A B = Σ {A} B

syntax Sigma A (λ x → b) = Σ x ꞉ A , b
infix -1 Sigma

pr₁-again : {A : Type} {B : A → Type} → Σ B → A
pr₁-again = pr₁
pr₂-again : {A : Type} {B : A → Type} ((x , y) : Σ B) → B x -- We can use pattern in the definition if the type has the η-rule
pr₂-again = pr₂

Σ-elim : {A : Type} {B : A → Type} {C : (Σ x ꞉ A , B x) → Type}
  → ((x : A) (y : B x) → C (x , y))
  → (z : Σ x ꞉ A , B x) → C z
Σ-elim f (x , y) = f x y

-- Σ-elim is an invertible rule
Σ-uncurry : {A : Type} {B : A → Type} {C : (Σ x ꞉ A , B x) → Type}
  → ((z : Σ x ꞉ A , B x) → C z)
  → (x : A) (y : B x) → C (x , y)
Σ-uncurry f x y = f (x , y)

_×_ : Type → Type → Type
A × B = Σ x ꞉ A , B
infixl 2 _×_

data _∔_ (A B : Type) : Type where
  inl : A → A ∔ B
  inr : B → A ∔ B
infix 20 _∔_

∔-elim : {A B : Type} {C : (A ∔ B) → Type}
  → ((x : A) → C (inl x))
  → ((x : B) → C (inr x))
  → (x : A ∔ B) → C x
∔-elim f g (inl x) = f x
∔-elim f g (inr x) = g x

∔-nondep-elim : {A B C : Type}
  → (A → C)
  → (B → C)
  → A ∔ B → C
∔-nondep-elim = ∔-elim

-- Truncated disjunction ∥ A ∔ B ∥

data _≡_ {A : Type} : A → A → Type where
  refl : (x : A) → x ≡ x
infix 0 _≡_

-- With K, pattern matching becomes equivalent to ≡-elim
≡-elim : {X : Type} {P : (x y : X) → x ≡ y → Type}
  → ((x : X) → P x x (refl x))
  → (x y : X) (p : x ≡ y) → P x y p
≡-elim f x .x (refl .x) = f x -- .x means Agda notice that there is an additional constraint on the second input: it has to be the same as x
```
