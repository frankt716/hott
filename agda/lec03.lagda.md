Trying to learn Agda through the [HoTTEST Summer School](https://github.com/martinescardo/HoTTEST-Summer-School).

```agda
{-# OPTIONS --without-K --safe #-}
module lec03 where
open import lec02 public
```

Last time, we talked about equalities. Equalities should be
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
We can prove `inf-many-primes` because for any `n`, we can always construct a prime number larger than `n`. It requires some effort though.
