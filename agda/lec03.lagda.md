Trying to learn Agda through the [HoTTEST Summer School](https://github.com/martinescardo/HoTTEST-Summer-School).

```agda
{-# OPTIONS --without-K --safe #-}
module lec03 where
open import lec01 hiding (𝟙 ; ⋆ ; _≣_)
open import lec02 using (is-prime ; _*_ ; 𝟙 ; ⋆ ; _≥_)
open import Agda.Primitive using (Level ; lzero ; lsuc ; _⊔_)
                           renaming (Set to 𝓤)
                           public
variable i j k : Level
```

Let's redefine a few thing with universes this time.
```agda
record Σ {A : 𝓤 i} (B : A → 𝓤 j) : 𝓤 (i ⊔ j) where
  constructor _,_
  field
    pr₁ : A
    pr₂ : B pr₁
open Σ public
infixr 1 _,_

Sigma : (A : 𝓤 i) (B : A → 𝓤 j) → 𝓤 (i ⊔ j)
Sigma {i} {j} A B = Σ {i} {j} {A} B

syntax Sigma A (λ x → b) = Σ x ꞉ A , b
infix -1 Sigma

_×_ : 𝓤 i → 𝓤 j → 𝓤 (i ⊔ j)
A × B = Σ x ꞉ A , B
infixr 2 _×_

¬_ : 𝓤 i → 𝓤 i
¬ A = A → 𝟘
```

```agda
data _≡_ {X : 𝓤 i} : X → X → 𝓤 i where
  refl : (x : X) → x ≡ x
infix 0 _≡_

_≢_ : {X : 𝓤 i} → X → X → 𝓤 i
A ≢ B = ¬ (A ≡ B)

≡-elim : {X : 𝓤 i} (A : (x y : X) → x ≡ y → 𝓤 j)
  → ((x : X) → A x x (refl x))
  → (x y : X) → (p : x ≡ y) → A x y p
≡-elim A f x .x (refl .x) = f x

≡-nondep-elim : {X : 𝓤 i} (A : X → X → 𝓤 j)
  → ((x : X) → A x x)
  → (x y : X) → x ≡ y → A x y
≡-nondep-elim A = ≡-elim (λ x y _ → A x y)

_∙_ : {X : 𝓤 i} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
p ∙ refl _ = p
infixl 7 _∙_

_⁻¹ : {X : 𝓤 i} {x y : X} → x ≡ y → y ≡ x
refl x ⁻¹ = refl x
infix 40 _⁻¹

ap : {A : 𝓤 i} {B : 𝓤 j} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f (refl x) = refl (f x)

transport : {A : 𝓤 i} (B : A → 𝓤 j) {x y : A} → x ≡ y → B x → B y
transport B (refl _) bₓ = bₓ
```

We can define the (sub)type of prime numbers.
```agda
ℙ : 𝓤₀
ℙ = Σ p ꞉ ℕ , is-prime p

ℙ-inclusion : ℙ → ℕ
ℙ-inclusion = pr₁
```

`ℙ-inclusion` is left-cancelable, i.e., is satisfies `ℙ-inclusion u ≡ ℙ-inclusion v → u ≡ v`. In fact, it is an embedding. This relies on the fact that `is-prime n` is a proposition (has exactly 1 inhabitant). Let's define (not quite) the type of composite numbers:
```agda
CN : 𝓤
CN = Σ x ꞉ ℕ , Σ (y , z) ꞉ ℕ × ℕ , (x ≡ y * z)

CN-projection : CN → ℕ
CN-projection = pr₁
```

`CN-projection` is not left-cancelable, and hence cannot be considered as an inclusion. The next counter-example demonstrates that `CN-projection` is not left-cancelable.
```agda
counterexample : CN-projection (6 , (3 , 2) , refl 6) ≡ CN-projection (6 , (2 , 3) , refl 6)
counterexample = refl 6
```

We will prove that the two tuples `(6 , (3 , 2))` and `(6 , (2 , 3)` are in fact *different*.
To get a (sub)type of composite numbers, we need to define the notion of truncation, which we will do later.

Another example use of the `Σ` type is the type of monoids. First, let's define what a `prop` and what a `set` is. A *proposition* is a type with at most one inhabitant. A *set* is a type in which the equality between any two inhabitants is a proposition (there is at most one way for any two inhabitants to be equal). 
```agda
is-prop : 𝓤 i → 𝓤 i
is-prop X = (x y : X) → x ≡ y

is-set : 𝓤 i → 𝓤 i
is-set X = (x y : X) → is-prop (x ≡ y)
```

Now let's define monoids.
```agda
Mon : 𝓤 (lsuc i)
Mon {i} = Σ X ꞉ 𝓤 i  -- data
  , is-set X  -- property
  × (Σ 𝟏 ꞉ X , -- data (but...)
     Σ _·_ ꞉ (X → X → X) -- data
       , ((x : X) → (x · 𝟏 ≡ x)) -- property
       × ((x : X) → (𝟏 · x ≡ x)) -- property
       × ((x y z : X) → (x · (y · z)) ≡ ((x · y) · z))) -- property
```

The type of monoid is not a set because two monoids can be equal (isomorphic) in more than one way. If we remove the requirement `is-set X`, then the resulting type is the type of ∞-monoids.

This can be defined with a record
```agda
record Monoid : 𝓤 (lsuc i) where
  constructor mon
  field
    carrier        : 𝓤 i
    carrier-is-set : is-set carrier
    𝟏              : carrier
    _·_            : carrier → carrier → carrier
    left-unit-law  : (x : carrier) → x · 𝟏 ≡ x
    right-unit-law : (x : carrier) → 𝟏 · x ≡ x
    assoc-law      : (x y z : carrier) → (x · (y · z)) ≡ ((x · y) · z)
```

We can prove that these two types are isomorphic.
```agda
α : Mon {i} → Monoid {i}
α (X , X-is-set , 𝟏 , _·_ , l , r , a) = mon X X-is-set 𝟏 _·_ l r a

β : Monoid {i} → Mon {i}
β (mon X X-is-set 𝟏 _·_ l r a) = (X , X-is-set , 𝟏 , _·_ , l , r , a)

αβ : (M : Monoid {i}) → α (β M) ≡ M
αβ = refl

βα : (M : Mon {i}) → β (α M) ≡ M
βα = refl
```

Records are not part of MLTT and HoTT so to define a monoid in HoTT, we use the definition with `Σ`.

In lecture 1, we had the following proof.
```agda
false-is-not-true[not-an-MLTT-proof] : false ≢ true
false-is-not-true[not-an-MLTT-proof] ()
```

However, this is a a MLTT proof. To prove this fact, we need a universe.
```agda
_≣_ : Bool → Bool → 𝓤₀
true ≣ true = 𝟙
true ≣ false = 𝟘
false ≣ true = 𝟘
false ≣ false = 𝟙

≡-gives-≣ : {x y : Bool} → x ≡ y → x ≣ y
≡-gives-≣ (refl true) = ⋆
≡-gives-≣ (refl false) = ⋆

false-is-not-true : false ≢ true
false-is-not-true = ≡-gives-≣
```

Let's try to prove that `0 ≢ 1` in MLTT style.
```agda
_≣ℕ_ : ℕ → ℕ → 𝓤₀
zero ≣ℕ zero = 𝟙
zero ≣ℕ succ m = 𝟘
succ n ≣ℕ zero = 𝟘
succ n ≣ℕ succ m = n ≣ℕ m

≣ℕ-refl : (x : ℕ) → x ≣ℕ x
≣ℕ-refl zero = ⋆
≣ℕ-refl (succ x) = ≣ℕ-refl x

≡-gives-≣ℕ : {x y : ℕ} → x ≡ y → x ≣ℕ y
≡-gives-≣ℕ (refl zero) = ⋆
≡-gives-≣ℕ (refl (succ x)) = ≣ℕ-refl x

0-≢-1 : 0 ≢ 1
0-≢-1 = ≡-gives-≣ℕ
```

When many functions share the same parameters, we can factor those parameters out and put them in a module.
```agda
module _ {X : 𝓤 i} {A : X → 𝓤 j} {(x , a) (y , b) : Σ A} where
  from-Σ-≡ : (x , a) ≡ (y , b)
           → Σ p ꞉ (x ≡ y) , (transport A p a ≡ b)
  from-Σ-≡ (refl (x , a)) = (refl x , refl a)

  to-Σ-≡ : (Σ p ꞉ (x ≡ y) , (transport A p a ≡ b))
         → (x , a) ≡ (y , b)
  to-Σ-≡ (refl x , refl a) = refl (x , a)
```
