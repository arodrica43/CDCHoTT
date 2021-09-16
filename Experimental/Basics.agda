{-# OPTIONS --cubical --without-K #-}
module CDCHoTT.Experimental.Basics where

open import Cubical.Foundations.Everything
open import Cubical.Data.Bool



{-
-- Flat

data ♭ {@♭ l : Level} (@♭ A : Type l) : Type l where
    _^♭ : (@♭ a : A) → ♭ A

♭-induction : ∀ {c : Level} {@♭ l : Level}{@♭ A : Type l}
         → (C : ♭ A → Type c)
         → ((@♭ u : A) → C (u ^♭))
         → (x : ♭ A) → C x
♭-induction C f (x ^♭) = f x

♭-counit : ∀ {@♭ l : Level} {@♭ A : Type l}
    → (♭ A → A)
♭-counit (x ^♭) = x

♭-counit-at : 
      ∀ (@♭ A : Type ℓ-zero)
    → (♭ A → A)
♭-counit-at A = ♭-counit {_} {A}
-}
