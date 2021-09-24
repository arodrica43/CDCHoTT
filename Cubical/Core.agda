{-# OPTIONS --without-K --cubical #-}

module CDCHoTT.Cubical.Core where

 {-
   This file is a dictionary to traduce between DCHoTT and Cubical Agda.
   It will be splitted in many files as necessary. This first file will contain the traduction between identity types.
 -}

  open import CDCHoTT.Basics
  open import CDCHoTT.EqualityAndPaths renaming (refl to rfl) 
  open import Cubical.Foundations.Everything


  ≡-is-≈ : ∀ {i} {A : U i}{x y : A} →  (x ≡ y) → (x ≈ y)
  ≡-is-≈ {x = x} p = J (λ s t → x ≈ s) rfl  p

  ≈-is-≡ : ∀ {i} {A : U i}{x y : A} →  (x ≈ y) → (x ≡ y)
  ≈-is-≡ rfl = refl

  ≡-≡ : ∀ {i} {A : U i}{x y : A} → (x ≡ y) → x ≡ y
  ≡-≡ p = ≈-is-≡ (≡-is-≈ p)

  ≈-≈ : ∀ {i} {A : U i}{x y : A} → (x ≈ y) → x ≈ y
  ≈-≈ p = ≡-is-≈ (≈-is-≡ p)

  ≈-id : ∀ {i} {A : U i}{x y : A}(p : x ≈ y) → ≈-≈ p ≈ p
  ≈-id {x = x} rfl = {!!}
  
  ≡-id : ∀ {i} {A : U i}{x y : A}(p : x ≡ y) → ≡-≡ p ≡ p
  ≡-id {x = x} p = λ i j → ≈-is-≡ (transp (λ k → x ≈ p {!i!} ) i0 {!!}) j
