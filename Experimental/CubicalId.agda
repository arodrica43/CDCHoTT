{-# OPTIONS --without-K --cubical #-}

module CDCHoTT.Experimental.CubicalId where

  open import CDCHoTT.Basics
  open import Cubical.Foundations.Everything

  infix 5 _≈_                                         -- \approx
  data _≈_ {i} {A : U i} (a : A) : A → U i where
    id : a ≈ a

  ≡-is-≈ : ∀ {i} {A : U i}{x y : A} →  (x ≡ y) → (x ≈ y)
  ≡-is-≈ {x = x} p = J (λ s t → x ≈ s) id p

  ≈-is-≡ : ∀ {i} {A : U i}{x y : A} →  (x ≈ y) → (x ≡ y)
  ≈-is-≡ id = refl

  ≡-≡ : ∀ {i} {A : U i}{x y : A} → (x ≡ y) → x ≡ y
  ≡-≡ p = ≈-is-≡ (≡-is-≈ p)

  ≈-≈ : ∀ {i} {A : U i}{x y : A} → (x ≈ y) → x ≈ y
  ≈-≈ p = ≡-is-≈ (≈-is-≡ p)

  ≈-id : ∀ {i} {A : U i}{x y : A}(p : x ≈ y) → ≈-≈ p ≈ p
  ≈-id {x = x} id = {!!}

  
  ≡-id : ∀ {i} {A : U i}{x y : A}(p : x ≡ y) → ≡-≡ p ≡ p
  ≡-id {x = x} p = λ i j → ≈-is-≡ (transp (λ k → x ≈ p {!i!} ) i0 {!!}) j
