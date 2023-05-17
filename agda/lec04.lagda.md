Trying to learn Agda through the [HoTTEST Summer School](https://github.com/martinescardo/HoTTEST-Summer-School).

A circle consists of a base point and a loop around the base point.
```agda
{-# OPTIONS --without-K --rewriting #-}
open import prelude

module lec04 where
  postulate
    S¹ : Type
    base : S¹
    loop : base ≡ base
```

To define a function out of a circle, it suffices to supply an element `x : X` and a loop around it `l : x ≡ x`. The function defined by the recursor `S¹-rec` ought to satisfy the following defining equalities:
- `(S¹-rec x l) base :≡ x`, and
- `ap (S¹-rec x l) loop :≡ l`.
The second equality does not quite type check in Agda because `ap (S¹-rec x l) loop : (S¹-rec x l) base ≡ (S¹-rec x l) base`, but `l : x ≡ x`. Agda does not know that we are treating `(S¹-rec x l) base ≡ x` as a definitional equality so we ask Agda to treat `(S¹-rec x l) base ≡ x` as a definitional equality, allowing us to assert what we want.
```agda
  postulate
    S¹-rec : {X : Type} (x : X) (l : x ≡ x) → S¹ → X
    S¹-rec-base : {X : Type} (x : X) (l : x ≡ x) → (S¹-rec x l) base ≡ x

  {-# BUILTIN REWRITE _≡_ #-}
  {-# REWRITE S¹-rec-base #-}
  postulate
    S¹-rec-loop : {X : Type} (x : X) (l : x ≡ x) → ap (S¹-rec x l) loop ≡ l
```

Alternatively, we can define a (two-point) circle as follows:
```agda
  postulate
    C¹ : Type
    north : C¹
    south : C¹
    west : north ≡ south
    east : north ≡ south

    C¹-rec : {X : Type} (n s : X) (w e : n ≡ s) → C¹ → X
    C¹-rec-north : {X : Type} (n s : X) (w e : n ≡ s) → (C¹-rec n s w e) north ≡ n
    C¹-rec-south : {X : Type} (n s : X) (w e : n ≡ s) → (C¹-rec n s w e) south ≡ s
  {-# REWRITE C¹-rec-north #-}
  {-# REWRITE C¹-rec-south #-}
  postulate
    C¹-rec-west : {X : Type} (n s : X) (w e : n ≡ s) → ap (C¹-rec n s w e) west ≡ w
    C¹-rec-east : {X : Type} (n s : X) (w e : n ≡ s) → ap (C¹-rec n s w e) east ≡ e
```

We can show that there are functions `to : S¹ ↔ C¹ : from`.
```agda
  to : S¹ → C¹
  to = S¹-rec north (east ∙ ! west)

  from : C¹ → S¹
  from = C¹-rec base base (refl _) loop

  from-to-north : to (from north) ≡ north
  from-to-north = refl _

  from-to-south : to (from south) ≡ south
  from-to-south = west

  to-from-base : from (to base) ≡ base
  to-from-base = refl _
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

  example : example-path ≡ loop [ base ≡ base [ S¹ ] ]
  example = (loop ∙ ! loop) ∙ loop ≡⟨ ap (λ H → H ∙ loop) (!-inv-r loop) ⟩
            refl _ ∙ loop ≡⟨ ∙-unit-l loop ⟩
            loop ∎
```

Let's write a function `S¹ → S¹`. This function winds around the same circle twice.
```agda
  double : S¹ → S¹
  double = S¹-rec base (loop ∙ loop)

  double-loop : ap double loop ≡ loop ∙ loop
  double-loop = S¹-rec-loop _ _

  ap-∙ : {A B : Type} {f : A → B} {x y z : A}
         (p : x ≡ y)
         (q : y ≡ z)
       → ap f (p ∙ q) ≡ ap f p ∙ ap f q
  ap-∙ (refl _) (refl _) = refl _

  double-2-loops : ap double (loop ∙ loop) ≡ loop ∙ loop ∙ (loop ∙ loop)
  double-2-loops =
    ap double (loop ∙ loop) ≡⟨ ap-∙ loop loop ⟩
    ap double loop ∙ ap double loop ≡⟨ ap₂ (λ p q → p ∙ q)
                                           (S¹-rec-loop _ _)
                                           (S¹-rec-loop _ _) ⟩
    (loop ∙ loop) ∙ (loop ∙ loop) ∎
```
