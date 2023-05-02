Trying to learn Agda through the [HoTTEST Summer School](https://github.com/martinescardo/HoTTEST-Summer-School).

```agda
{-# OPTIONS --without-K --safe #-}
module lec02 where
open import lec01 hiding (𝟙 ; 𝟙-elim ; 𝟙-nondep-elim)
```

We can define ¬ in terms of 𝟘.
```agda
¬_ : Type → Type
¬ A = A → 𝟘
infix 1000 ¬_

is-empty : Type → Type
is-empty A = A → 𝟘

𝟘-is-empty : is-empty 𝟘
𝟘-is-empty = λ x → x
```

We redefine the unit type `𝟙` using a record. The advantage of this is that definitions of this kind satisfy the η-law. In this case, the η-law says that any term of type `𝟙` is `⋆`.
```agda
record 𝟙 : Type where
  constructor
    ⋆
open 𝟙 public

𝟙-elim : {P : 𝟙 → Type}
  → P ⋆
  → (x : 𝟙) → P x
-- Goal: P x
𝟙-elim b x = b
--     ↑ b : P ⋆
-- We don't need to do a pattern match because Agda knows that x has to be ⋆.

𝟙-nondep-elim : {P : Type}
  → P
  → 𝟙 → P
𝟙-nondep-elim = 𝟙-elim

𝟙-is-nonempty : ¬ (is-empty 𝟙)
𝟙-is-nonempty f = f ⋆
```

The two element type `𝟚`. Note that it can't be defined with a record because it has two constructors.
`𝟚` is essentially the `Bool` type. We'll make this precise when we talk about isomorphisms.
```agda
data 𝟚 : Type where
  𝟎 𝟏 : 𝟚
  
𝟚-elim : {A : 𝟚 → Type}
  → A 𝟎
  → A 𝟏
  → (x : 𝟚) → A x
𝟚-elim a₀ a₁ 𝟎 = a₀
𝟚-elim a₀ a₁ 𝟏 = a₁

𝟚-nondep-elim : {A : Type}
  → A
  → A
  → 𝟚 → A
𝟚-nondep-elim = 𝟚-elim
```

We can define some syntax for `(x : A) → B x` to make it more similar to hott. Unfortunately, we cannot use `:` in the syntax because it's reserved by Agda, so the closest thing we can use is `꞉` (\:4).
```agda
Pi : (A : Type) (B : A → Type) → Type
Pi A B = (x : A) → B x

syntax Pi A (λ x → b) = Π x ꞉ A , b
```

The usual composition is given in an anonymous private module. We can extend function composition to depedent functions. Given `f : A → B` and `g : Π x : B , C x`, we can compose them and get `g ∘ f : Π x : A , C (f x)`.
```agda
module _ where private
  _∘_ : {A B C : Type} → (B → C) → (A → B) → (A → C)
  (g ∘ f) x = g (f x)

-- Function composition with depedent type
_∘_ : {A B : Type} {C : B → Type}
  → (Π x ꞉ B , C x)
  → (f : A → B)
  → Π x ꞉ A , C (f x)
(g ∘ f) x = g (f x)
```

We can define the `Σ` type with `data`. We can define projections out of a `Σ` type in terms of its eliminator.
```agda
module _ where private
  data Σ {A : Type} (B : A → Type) : Type where
    _,_ : (x : A) (y : B x) → Σ {A} B
    
  Σ-elim : {A : Type} {B : A → Type} {C : (Σ {A} B) → Type}
    → ((x : A) (y : B x) → C (x , y))
    → (s : Σ {A} B) → C s
  Σ-elim f (x , y) = f x y

  pr₁ : {A : Type} {B : A → Type} → Σ B → A
  pr₁ {A} {B} = Σ-elim h where
    h : (x : A) (y : B x) → A
    h x _ = x
  pr₂ : {A : Type} {B : A → Type} → (s : Σ B) → B (pr₁ s)
  pr₂ {A} {B} = Σ-elim h where
    h : (x : A) (y : B x) → B x
    h _ y = y
```

Alternatively, we can define the `Σ` type with a record. Here `π₁ : (Σ x : A , B) → A` and `π₂ : (s : Σ x : A , B) → B (π₁ s)`, making it a negative type *I think* (correct me if I'm wrong).
```agda
record Σ {A : Type} (B : A → Type) : Type where
  constructor _,_
  field
    π₁ : A
    π₂ : B π₁

open Σ public
infixr 0 _,_

Sigma : (A : Type) (B : A → Type) → Type
Sigma A B = Σ {A} B

syntax Sigma A (λ x → b) = Σ x ꞉ A , b
infix -1 Sigma

pr₁-again : {A : Type} {B : A → Type}
  → (Σ x ꞉ A , B x) → A
pr₁-again = π₁

pr₂-again : {A : Type} {B : A → Type}
  → (s : Σ x ꞉ A , B x)
  → B (π₁ s)
pr₂-again = π₂
```

In fact, since `Σ` admits the η-law, we can pattern match in the *type* declaration.
```agda
pr₂-again' : {A : Type} {B : A → Type}
  → ((x , y) : Σ x ꞉ A , B x)
  → B x
pr₂-again' = π₂
```

Eariler, we defined projections in terms of `Σ-elim`. Let's try to define `Σ-elim` in terms of its projections.
```agda
Σ-elim : {A : Type} {B : A → Type} {C : (Σ x ꞉ A , B x) → Type}
  → ((x : A) (y : B x) → C (x , y))
  → (s : (Σ x ꞉ A , B x)) → C s
Σ-elim f s = f (π₁ s) (π₂ s)
```

Interestingly, the elimination principle is invertible. I might have gotten the order of curry and uncurry wrong but whatever.
```agda
Σ-uncurry : {A : Type} {B : A → Type} {C : (Σ x ꞉ A , B x) → Type}
  → ((z : Σ x ꞉ A , B x) → C z)
  → (x : A) (y : B x) → C (x , y)
Σ-uncurry f x y = f (x , y)
```

The product type is a special case of the dependent product type.
```agda
_×_ : Type → Type → Type
A × B = Σ x ꞉ A , B
infixl 2 _×_
```

The dual of a product is a coproduct. Let's define it.
```agda
data _∔_ (A B : Type) : Type where
  inl : A → A ∔ B
  inr : B → A ∔ B

∔-elim : {A B : Type} {C : A ∔ B → Type}
  → ((x : A) → C (inl x))
  → ((x : B) → C (inr x))
  → (x : A ∔ B) → C x
∔-elim f g (inl x) = f x
∔-elim f g (inr x) = g x

∔-nondep-elim : {A B C : Type}
  → (A → C)
  → (B → C)
  → (A ∔ B → C)
∔-nondep-elim = ∔-elim
```

Finally, let's define the identity type. The elimination principle for the identity type is also known as *path induction*.
```agda
data _≡_ {A : Type} : A → A → Type where
  refl : (x : A) → x ≡ x
infix 0 _≡_

≡-elim : {A : Type} {B : {x y : A} → x ≡ y → Type}
  → ({x : A} → B (refl x))
  → {x y : A} → (p : x ≡ y) → B p
≡-elim f (refl _) = f

≡-nondep-elim : {A : Type} {B : A → A → Type}
  → ({x : A} → B x x)
  → {x y : A} → x ≡ y → B x y
≡-nondep-elim = ≡-elim
```
Apparently, without axiom K, `≡-elim` is equivalent to pattern matching. I've not figured out what that means exactly though.

We talked about equalities. Equalities should be
- Reflexive
- Symmetric
- Transitive

Well, reflexivity should be easy.
```agda
≡-refl : {A : Type} {x : A} → x ≡ x
≡-refl {A} {x} = refl x

≡-sym : {A : Type} {x y : A}
  → x ≡ y → y ≡ x
≡-sym (refl x) = refl x

≡-tran : {A : Type} {x y z : A}
  → x ≡ y → y ≡ z → x ≡ z
≡-tran p (refl _) = p
```
In `≡-tran`, we could've done induction on the first path (or both).

We expect that applying a function to two (typically) equal terms results in (typically) equal terms. This corresponds to `f_equal` in Coq.
```agda
ap : {A B : Type} (f : A → B) {x y : A} →  x ≡ y → f x ≡ f y
ap f (refl x) = refl (f x)
```

An important operation is `transport` (Leibniz principle), which is `rewrite` in Coq
```agda
transport : {A : Type} {B : A → Type}
  → {x y : A}
  → x ≡ y
  → B x → B y
transport (refl x) a = a
```

The traditional notion for
- `≡-tran` is `∙`
- `≡-sym` is `_⁻¹`
```agda
_∙_ : {A : Type} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ = ≡-tran

infixl 7 _∙_

_⁻¹ : {A : Type} {x y : A} → x ≡ y → y ≡ x
_⁻¹ = ≡-sym

infix 40 _⁻¹
```

Ok. Let's define a few things on `ℕ`.
```agda
_≤_ : ℕ → ℕ → Type
zero ≤ y = 𝟙
succ x ≤ zero = 𝟘
succ x ≤ succ y = x ≤ y

_≥_ : ℕ → ℕ → Type
x ≥ y = y ≤ x

infixr 30 _*_
_*_ : ℕ → ℕ → ℕ
zero * y = 0
succ x * y = x * y + y

_divides_ : ℕ → ℕ → Type
x divides y = Σ z ꞉ ℕ , x * z ≡ y

is-prime : ℕ → Type
is-prime p = (p ≥ 2) × ((n : ℕ) → n divides p → (n ≡ 1) ∔ (n ≡ p))

twin-prime-conjecture : Type
twin-prime-conjecture = (n : ℕ) → Σ p ꞉ ℕ , (p ≥ n)
                                          × is-prime p
                                          × is-prime (p + 2)

inf-many-primes : Type
inf-many-primes = (n : ℕ) → Σ p ꞉ ℕ , (p ≥ n) × is-prime p
```
We can prove `inf-many-primes` because for any `n`, we can construct a prime number larger than `n`. The construction goes as follows: for any `n`, compute a list of prime numbers at most `n`, compute the product of these prime numbers and then add 1 to it. This is a prime number larger than `n`.

```agda
+-zero : (n : ℕ) → n + 0 ≡ n
+-zero zero = refl zero
+-zero (succ n) = ap succ (+-zero n)

+-succ-comm : (n m : ℕ) → succ n + m ≡ n + (succ m)
+-succ-comm zero m = refl (succ m)
+-succ-comm (succ n) m = ap succ (+-succ-comm n m)

+-comm : (n m : ℕ) → n + m ≡ m + n
+-comm zero m = (+-zero m)⁻¹
+-comm (succ n) m = p₁ ∙ p₂ where
  p₁ : succ (n + m) ≡ succ (m + n)
  p₁ = ap succ (+-comm n m)
  p₂ : succ (m + n) ≡ m + (succ n)
  p₂ = +-succ-comm m n

+-assoc : (a b c : ℕ) → a + b + c ≡ a + (b + c)
+-assoc zero b c = refl (b + c)
+-assoc (succ a) b c = ap succ (+-assoc a b c)
```
