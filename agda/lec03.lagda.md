Trying to learn Agda through the [HoTTEST Summer School](https://github.com/martinescardo/HoTTEST-Summer-School).

```agda
{-# OPTIONS --without-K --safe #-}
module lec03 where
open import lec01 hiding (𝟙 ; ⋆ ; _≣_)
open import lec02 using (is-prime ; _*_ ; 𝟙 ; ⋆)
open import Agda.Primitive using (Level ; lzero ; lsuc ; _⊔_)
                           renaming (Set to 𝓤)
                           public
variable i j k : Level
```
