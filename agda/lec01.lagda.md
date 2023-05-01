Trying to learning Agda through the [HoTTEST Summer School](https://github.com/martinescardo/HoTTEST-Summer-School).

The K axiom is not consistent with hott so we need to turn it off. We also need to turn off experimental features to avoid inconsistency.
```agda
{-# OPTIONS --without-K --safe #-} 
```
In Agda, types are Set. We redefine this so it's more consistent with hott's terminology.
```agda
module lec01 where

Type = Set
```

`Bool` is a simple data type. To define a type, we define its introduction elimination rules.
```agda
data Bool : Type where
  true false : Bool

Bool-elim : {A : Bool → Type}
  → A true
  → A false
  → (x : Bool) → A x
Bool-elim tt ff true = tt
Bool-elim tt ff false = ff

Bool-nondep-elim : {A : Type} → A → A → Bool → A
Bool-nondep-elim = Bool-elim
```

- C-c C-, to show context.
- C-c C-c to pattern match.
- C-c C-SPC to fill hole
- More shortcuts can be found [here](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html).

The nondep eliminator for `Bool` is the if _ then _ else _ construct. We can have a dependent version, too.
```agda
if_then_else_ : {A : Type} → Bool → A → A → A
if b then x else y = Bool-nondep-elim x y b

if[_]_then_else_ : (A : Bool → Type)
  → (x : Bool)
  → A true
  → A false
  → A x
if[ A ] b then x else y = Bool-elim {A} x y b
```
Let's define the natural number type.
```agda
data ℕ : Type where
  zero : ℕ
  succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}
```

The elimination principle is the familiar mathematical induction. The nondep version is primitive recursion. Let's define the nondep explicitly rather than using ℕ-elim.
Recall that to define a function `g : ℕ → A`, we need
- a base case `z`
- a "next step" function `f : ℕ → A → A`
so we have `g 0 = z`, `g 1 = f 0 z`, `g 2 = f 1 (f 0 z)`, ...
```agda
ℕ-elim : {A : ℕ → Type}
  → A zero
  → ((n : ℕ) → A n → A (succ n))
  → (n : ℕ) → A n
ℕ-elim z f zero = z
ℕ-elim z f (succ n) = f n (ℕ-elim z f n)

ℕ-nondep-elim : {A : Type}
  → A
  → (ℕ → A → A)
  → ℕ → A
ℕ-nondep-elim a f n = f n a
```

Let's define the addition function.
```agda
_+_ : ℕ → ℕ → ℕ
zero + y = y
succ x + y = succ (x + y)
```

Now, we define list. The list type family is indexed by a type, allowing us to have a list of naturals, a list of lists, etc.
Note that the nondep version of `List-elim` is the usual `fold`. 
```agda
data List (A : Type) : Type where
  [] : List A
  _::_ : A → List A → List A
infixr 10 _::_

List-elim : {X : Type} {A : List X → Type}
  → A []
  → ((x : X) (xs : List X) → A xs → A (x :: xs))
  → (xs : List X) → A xs
List-elim a₀ f [] = a₀
List-elim a₀ f (x :: xs) = f x xs (List-elim a₀ f xs)

List-nondep-elim : {X A : Type}
  → A
  → (X → List X → A → A)
  → List X → A
List-nondep-elim = List-elim

sample-list₀ : List ℕ
sample-list₀ = 0 :: 1 :: 2 :: 3 :: []
```

We can define the `length` function. We can also define it using `List-elim`.
```agda
length : {X : Type} → List X → ℕ
length [] = 0
length (_ :: xs) = succ (length (xs))

length' : {X : Type} → List X → ℕ
-- The length of x :: xs is succ x₁ where x₁ is the length of xs
--                            ↓
length' = List-elim 0 (λ _ _ x₁ → succ x₁)
--                  ↑
-- the empty list has length 0
```

Let's define the list concatenation function.
```agda
_++_ : {X : Type} → List X → List X → List X
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)
```

Now, let's define the empty type and the unit type.
```agda
data 𝟘 : Type where

𝟘-elim : {A : 𝟘 → Type}
  → (x : 𝟘) → A x
𝟘-elim ()

𝟘-nondep-elim : {A : Type} → 𝟘 → A
𝟘-nondep-elim ()

data 𝟙 : Type where
  ⋆ : 𝟙

𝟙-elim : {A : 𝟙 → Type}
  → A ⋆
  → (x : 𝟙) → A x
𝟙-elim a₀ ⋆ = a₀

𝟙-nondep-elim : {A : Type} → A → 𝟙 → A
𝟙-nondep-elim = 𝟙-elim
```

Now, let's define a specialized equality type on ℕ and prove that `x ≣ x` for all `x : ℕ`.
```agda
_≣_ : ℕ → ℕ → Type
zero ≣ zero = 𝟙
zero ≣ succ y = 𝟘
succ x ≣ zero = 𝟘
succ x ≣ succ y = x ≣ y
infix 0 _≣_

ℕ-refl : (x : ℕ) → x ≣ x
ℕ-refl zero = ⋆
ℕ-refl (succ x) = ℕ-refl x
```

Finally, we can prove that `length` is a monoid homomorphism. We use the `where` notation here to illustrate that you can write your proof this way.
```agda
lh : {X : Type} (xs ys : List X) → length (xs ++ ys) ≣ length xs + length ys
lh [] ys = ℕ-refl (length ys)
lh (x :: xs) ys = h where
  h : length (xs ++ ys) ≣ (length xs + length ys)
  h = lh xs ys
```
