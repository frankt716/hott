Trying to learning Agda through the [HoTTEST Summer School](https://github.com/martinescardo/HoTTEST-Summer-School).

The $K$ axiom.
```agda
{-# OPTIONS --without-K --safe #-} 

module lec01 where

Type = Set

data Bool : Type where
  true false : Bool

not : Bool → Bool
not true = false
not false = true

-- C-c C-, to show context
-- C-c C-c to pattern match
-- C-c C-SPC to fill hole
not' : Bool → Bool
not' true = false
not' false = true

idBool : Bool → Bool
idBool x = x

-- C-c C-s to solve constraints
idBool' : Bool → Bool
idBool' = λ (x : Bool) → x

-- This is a Π type
id' : (X : Type) → X → X
id' X x = x

-- With implicit argument
id : {X : Type} → X → X
id x = x

-- Use curly braces to supply implicit argument explicitly
idBool'' : Bool → Bool
idBool'' = id {Bool}

-- Or you can just omit it
idBool''' : Bool → Bool
idBool''' = id

-- If we use id' we can ask Agda to figure things out
idBool'''' : Bool → Bool
idBool'''' = id' _

-- If _ is on the left hand side, it means don't give it a name
example : {P Q : Type} → P → (Q → P)
example {P} {Q} p = f
  where
    f : Q → P
    f _ = p

example' : {P Q : Type} → P → (Q → P)
example' p = λ q → p

open import binary-products

ex : {P Q : Type} → P × Q → Q × P
ex (p , q) = (q , p)

-- "\bN"
data ℕ : Type where
  zero : ℕ
  succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

D : Bool → Type
D true = ℕ
D false = Bool

-- "mix-fix" operator
if_then_else_ : {X : Type} → Bool → X → X → X
if true  then x else y = x
if false then x else y = y

if[_]_then_else_ : (X : Bool → Type) → (b : Bool) → X true → X false → X b
if[ X ] true then x else y = x
if[ X ] false then x else y = y

-- Π (b : Bool), D b
weird : (b : Bool) → D b
weird b = if[ D ] b then 3 else false

-- Lists
data List (A : Type) : Type where
  [] : List A
  _::_ : A → List A → List A

infixr 10 _::_

sample-list₀ : List ℕ
sample-list₀ = 0 :: 1 :: 2 :: 3 :: []

length : {X : Type} → List X → ℕ
length [] = 0
length (_ :: xs) = succ (length (xs))

-- In MMTT there is no definition by recursion, but we have elimination principles

-- The elimination principle of the natural number (principle of induction)
ℕ-elim :
  {P : ℕ → Type}
  → P 0
  → ((k : ℕ) → P k → P (succ k))
  → (n : ℕ) → P n
ℕ-elim {P} p₀ f = h
  where
    h : (n : ℕ) → P n
    h zero = p₀
    h (succ n) = f n IH
      where
        IH : P n
        IH = h n

List-elim :
  {X : Type} {P : List X → Type}
  → P []
  → ((x : X) (xs : List X) → P xs → P (x :: xs))
  → (xs : List X) → P xs
List-elim pnil f [] = pnil
List-elim pnil f (x :: xs) = f x xs (List-elim pnil f xs)

data 𝟘 : Type where

data 𝟙 : Type where
  ⋆ : 𝟙

_≡ℕ_ : ℕ → ℕ → Type
zero ≡ℕ zero = 𝟙
zero ≡ℕ succ y = 𝟘
succ x ≡ℕ zero = 𝟘
succ x ≡ℕ succ y = x ≡ℕ y
infix 0 _≡ℕ_

ℕ-refl : (x : ℕ) → x ≡ℕ x
ℕ-refl zero = ⋆
ℕ-refl (succ x) = ℕ-refl x

_++_ : {A : Type} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

_+_ : ℕ → ℕ → ℕ
zero + y = y
succ x + y = succ (x + y)

lh : {X : Type} (xs ys : List X)
  → length (xs ++ ys) ≡ℕ length xs + length ys
lh [] ys = ℕ-refl (length ys)
lh (x :: xs) ys = lh xs ys
```
