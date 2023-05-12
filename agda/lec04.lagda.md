Trying to learn Agda through the [HoTTEST Summer School](https://github.com/martinescardo/HoTTEST-Summer-School).

```agda
{-# OPTIONS --without-K --rewriting #-}
open import prelude

module lec04 where
  postulate
    S1 : Type
    base : S1
    loop : base ≡ base
```

Groupoid laws and their applications.
```agda
  ∙-assoc : {A : Type} {a b c d : A} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
          → (p ∙ (q ∙ r)) ≡ ((p ∙ q) ∙ r) [ a ≡ d [ A ] ]
  ∙-assoc (refl _) (refl _) (refl _) = refl _

  ∙-unit-l : {A : Type} {x y : A}
           → (p : x ≡ y)
           → (refl _ ∙ p) ≡ p
  ∙-unit-l (refl _) = refl _

  ∙-unit-r : {A : Type} {x y : A}
           → (p : x ≡ y)
           → (p ∙ refl _) ≡ p
  ∙-unit-r p = refl p

  !-inv-l : {A : Type} {x y : A}
          → (p : x ≡ y)
          → (! p ∙ p) ≡ refl _
  !-inv-l (refl _) = refl _

  !-inv-r : {A : Type} {x y : A}
          → (p : x ≡ y)
          → (p ∙ ! p) ≡ refl _
  !-inv-r (refl _) = refl _
  
  example-path : base ≡ base
  example-path = loop ∙ ! loop ∙ loop

  example : example-path ≡ loop [ base ≡ base [ S1 ] ]
  example = (loop ∙ ! loop) ∙ loop ≡⟨ ap (λ H → H ∙ loop) (!-inv-r loop) ⟩
            refl _ ∙ loop ≡⟨ ∙-unit-l loop ⟩
            loop ∎
```

Circle recursion. To define a function from the circle type `S1` into another type `X`, provide `x : X` to serve as the "base point" and a path `l : x ≡ x` to serve as the "loop".
```agda
  postulate
    S1-rec : {X : Type} (x : X) (l : x ≡ x [ X ]) → (S1 → X)
    S1-rec-base : {X : Type} (x : X) (l : x ≡ x)
                → (S1-rec x l) base ≡ x

  {-# BUILTIN REWRITE _≡_ #-}
  {-# REWRITE S1-rec-base #-}
  postulate
    S1-rec-loop : {X : Type} (x : X) (l : x ≡ x)
                → ap (S1-rec x l) loop ≡ l
```

Let write a function `S1 → S1`. This function winds around the same circle twice.
```agda
  double : S1 → S1
  double = S1-rec base (loop ∙ loop)

  double-loop : ap double loop ≡ loop ∙ loop
  double-loop = S1-rec-loop _ _

  ap-∙ : {A B : Type} {f : A → B} {x y z : A}
         (p : x ≡ y)
         (q : y ≡ z)
       → ap f (p ∙ q) ≡ ap f p ∙ ap f q
  ap-∙ (refl _) (refl _) = refl _

  double-2-loops : ap double (loop ∙ loop) ≡ loop ∙ loop ∙ (loop ∙ loop)
  double-2-loops =
    ap double (loop ∙ loop) ≡⟨ ap-∙ loop loop ⟩
    ap double loop ∙ ap double loop ≡⟨ ap₂ (λ p q → p ∙ q)
                                           (S1-rec-loop _ _)
                                           (S1-rec-loop _ _) ⟩
    (loop ∙ loop) ∙ (loop ∙ loop) ∎
```

Let's define a two point circle.
```agda
  postulate
    Circle2 : Type
    north : Circle2
    south : Circle2
    west : north ≡ south
    east : north ≡ south
    Circle2-rec : {X : Type} (n : X) (s : X) (w : n ≡ s) (e : n ≡ s)
                → Circle2 → X

    Circle2-rec-north : {X : Type} (n : X) (s : X) (w : n ≡ s) (e : n ≡ s)
                      → Circle2-rec n s w e north ≡ n
    Circle2-rec-south : {X : Type} (n : X) (s : X) (w : n ≡ s) (e : n ≡ s)
                      → Circle2-rec n s w e south ≡ s
                      
  {-# REWRITE Circle2-rec-north #-}
  {-# REWRITE Circle2-rec-south #-}
  postulate
    Circle2-rec-west : {X : Type} (n : X) (s : X) (w : n ≡ s) (e : n ≡ s)
                     → ap (Circle2-rec n s w e) west ≡ w
    Circle2-rec-east : {X : Type} (n : X) (s : X) (w : n ≡ s) (e : n ≡ s)
                     → ap (Circle2-rec n s w e) east ≡ e

  to : S1 → Circle2
  to = S1-rec north (east ∙ ! west)

  from : Circle2 → S1
  from = Circle2-rec base base (refl _) loop

  from-to-north : to (from north) ≡ north
  from-to-north = refl north

  from-to-south : to (from south) ≡ south
  from-to-south = west
```
